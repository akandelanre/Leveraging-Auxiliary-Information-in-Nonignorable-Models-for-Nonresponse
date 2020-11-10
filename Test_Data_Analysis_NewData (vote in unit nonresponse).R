
###########################################################################
###########################################################################
################# Analysis on Latest (March 9 2020) Data ##################
############################## MD-U Model #################################
###########################################################################
###########################################################################

###### 1: Clear environment and load libraries
rm(list = ls())
set.seed(1234)
library(runjags)
library(coda)
library(xtable)
library(dplyr)
library(plotly)
library(ggplot2)

###### 2: Create functions for getting posterior summaries from matrix of posterior samples
Post_Summary <- function(PostMatrix){ #row=number of samples, column=number of parameters
  Postmean <- apply(PostMatrix,2,mean)
  Postsd <- apply(PostMatrix,2,sd) 
  PostCI <- t(apply(PostMatrix,2,quantile,prob=c(.025,.975)))
  Postsum <- cbind(Postmean,Postsd,PostCI)
  colnames(Postsum)[1:2] <- c("Post mean" , "Post std dev")
  return(Postsum)
}

# Using imputations
ProbVote_Imp <- function(Data,state){
  n <- length(state)
  ImpData <- data.frame(matrix(Data,nrow=n))
  colnames(ImpData) <- c("age","gender","vote")
  ImpData <- cbind(data.frame(state=state),ImpData)
  
  VoteBySubgroups <- c(by(ImpData,list(state=ImpData$state),function(x) sum(x$vote==1)/length(x$vote)),
                       by(ImpData,list(state=ImpData$state,gender=ImpData$gender),function(x) sum(x$vote==1)/length(x$vote)),
                       by(ImpData,list(state=ImpData$state,age=ImpData$age),function(x) sum(x$vote==1)/length(x$vote)),
                       by(ImpData,list(state=ImpData$state,age=ImpData$age,gender=ImpData$gender),function(x) sum(x$vote==1)/length(x$vote)) )
  
  SubgroupsByVote <- c(c(t(matrix(unlist( by(ImpData[ImpData$vote==1,],
                                             list(vote=ImpData$vote[ImpData$vote==1],state=ImpData$state[ImpData$vote==1]), function(x) 
                                               table(x$gender)/sum(table(x$gender))) ),nrow=2))),
                       c(t(matrix(unlist( by(ImpData[ImpData$vote==1,],
                                             list(vote=ImpData$vote[ImpData$vote==1],state=ImpData$state[ImpData$vote==1]), function(x) 
                                               table(x$age)/sum(table(x$age))) ),nrow=4))),
                       c(t(matrix(unlist( by(ImpData[ImpData$vote==1,],
                                             list(vote=ImpData$vote[ImpData$vote==1],state=ImpData$state[ImpData$vote==1]), function(x)
                                               c(t(table(x$gender,x$age)/sum(table(x$gender,x$age))))) ),nrow=8)))  )
  
  VoteBySubgroupsVAR <- c(by(ImpData,list(state=ImpData$state),
                             function(x) (sum(x$vote==1)/length(x$vote)^2)*(1-(sum(x$vote==1)/length(x$vote)))),
                          by(ImpData,list(state=ImpData$state,gender=ImpData$gender),
                             function(x) (sum(x$vote==1)/length(x$vote)^2)*(1-(sum(x$vote==1)/length(x$vote)))),
                          by(ImpData,list(state=ImpData$state,age=ImpData$age),
                             function(x) (sum(x$vote==1)/length(x$vote)^2)*(1-(sum(x$vote==1)/length(x$vote)))),
                          by(ImpData,list(state=ImpData$state,age=ImpData$age,gender=ImpData$gender),
                             function(x) (sum(x$vote==1)/length(x$vote)^2)*(1-(sum(x$vote==1)/length(x$vote)))) )
  
  return(list(VoteBySubgroups=VoteBySubgroups,SubgroupsByVote=SubgroupsByVote,VoteBySubgroupsVAR=VoteBySubgroupsVAR))
}

ProbVoteNonrespondents_Imp <- function(Data,state,unit){
  n <- length(state)
  ImpData <- data.frame(matrix(Data,nrow=n))
  colnames(ImpData) <- c("age","gender","vote")
  ImpData <- cbind(data.frame(state=state),ImpData)
  ImpData <- ImpData[unit==1,]
  
  ProbTurnout_NonResp <- c(by(ImpData,list(state=ImpData$state),function(x) sum(x$vote==1)/length(x$vote)) )

  ProbTurnout_NonRespVAR <- c(by(ImpData,list(state=ImpData$state),
                             function(x) (sum(x$vote==1)/length(x$vote)^2)*(1-(sum(x$vote==1)/length(x$vote)))) )
  
  return(list(ProbTurnout_NonResp=ProbTurnout_NonResp,ProbTurnout_NonRespVAR=ProbTurnout_NonRespVAR))
}

# Using posterior samples directly
PostPred_ContTable <- function(PostParameters,State){
  n <- length(State)
  NewData <- data.frame(state=State)
  
  beta_gender1 <- PostParameters[c("beta_gender1")]
  beta_gender2 <- PostParameters[c("beta_gender2[1]","beta_gender2[2]","beta_gender2[3]","beta_gender2[4]")]
  pi_gender <- beta_gender1 + beta_gender2[NewData$state]
  pi_gender <- 1/(exp(-pi_gender)+1)
  pi_gender <- cbind(1-pi_gender,pi_gender)
  Ran_unif_gender <- runif(nrow(pi_gender))
  cumul_gender <- pi_gender%*%upper.tri(diag(ncol(pi_gender)),diag=TRUE)
  NewData$gender <- rowSums(Ran_unif_gender>cumul_gender)
  
  pi_age <- cumm_pi_age <- matrix(0,ncol=4,nrow=n)
  beta_age1 <- PostParameters[c("beta_age1[1]","beta_age1[2]","beta_age1[3]")]
  beta_age2 <- PostParameters[c("beta_age2[1]","beta_age2[2]","beta_age2[3]","beta_age2[4]")]
  beta_age3 <- PostParameters[c("beta_age3")]
  cumm_pi_age[,1] <- beta_age1[1] + beta_age2[NewData$state] + beta_age3*NewData$gender
  cumm_pi_age[,1] <- 1/(exp(-cumm_pi_age[,1])+1)
  pi_age[,1] <- cumm_pi_age[,1]
  for(j in 2:3){
    cumm_pi_age[,j] <- beta_age1[j] + beta_age2[NewData$state] + beta_age3*NewData$gender
    cumm_pi_age[,j] <- 1/(exp(-cumm_pi_age[,j])+1)
    pi_age[,j] <- cumm_pi_age[,j] - cumm_pi_age[,j-1]
  }
  pi_age[,4] <- 1 - cumm_pi_age[,3]
  Ran_unif_age <- runif(nrow(pi_age))
  cumul_age <- pi_age%*%upper.tri(diag(ncol(pi_age)),diag=TRUE)
  NewData$age <- rowSums(Ran_unif_age>cumul_age) + 1L
  
  beta_vote1 <- PostParameters[c("beta_vote1")]
  beta_vote2 <- PostParameters[c("beta_vote2[1]","beta_vote2[2]","beta_vote2[3]","beta_vote2[4]")]
  beta_vote3 <- PostParameters[c("beta_vote3[1]","beta_vote3[2]","beta_vote3[3]","beta_vote3[4]")]
  beta_vote4 <- PostParameters[c("beta_vote4")]
  beta_vote5 <- matrix(0,ncol=4,nrow=4)
  beta_vote5[1,] <- PostParameters[c("beta_vote5[1,1]","beta_vote5[1,2]","beta_vote5[1,3]","beta_vote5[1,4]")]
  beta_vote5[2,] <- PostParameters[c("beta_vote5[2,1]","beta_vote5[2,2]","beta_vote5[2,3]","beta_vote5[2,4]")]
  beta_vote5[3,] <- PostParameters[c("beta_vote5[3,1]","beta_vote5[3,2]","beta_vote5[3,3]","beta_vote5[3,4]")]
  beta_vote5[4,] <- PostParameters[c("beta_vote5[4,1]","beta_vote5[4,2]","beta_vote5[4,3]","beta_vote5[4,4]")]
  pi_vote <- beta_vote1 + beta_vote2[NewData$state] + beta_vote3[NewData$age] + 
    beta_vote4*NewData$gender + c(unlist(lapply(c(1:n),function(x) beta_vote5[NewData$state[x],NewData$age[x]])))
  pi_vote <- 1/(exp(-pi_vote)+1)
  pi_vote <- cbind(1-pi_vote,pi_vote)
  Ran_unif_vote <- runif(nrow(pi_vote))
  cumul_vote <- pi_vote%*%upper.tri(diag(ncol(pi_vote)),diag=TRUE)
  NewData$vote <- rowSums(Ran_unif_vote>cumul_vote)
  
  beta_W1 <- PostParameters[c("beta_W1")]
  beta_W2 <- PostParameters[c("beta_W2[1]","beta_W2[2]","beta_W2[3]","beta_W2[4]")]
  beta_W3 <- PostParameters[c("beta_W3[1]","beta_W3[2]","beta_W3[3]","beta_W3[4]")]
  beta_W4 <- PostParameters[c("beta_W4")]
  pi_W <- beta_W1 + beta_W2[NewData$state] + beta_W3[NewData$age] + beta_W4*NewData$vote
  pi_W <- 1/(exp(-pi_W)+1)
  pi_W <- cbind(1-pi_W,pi_W)
  Ran_unif_W <- runif(nrow(pi_W))
  cumul_W <- pi_W%*%upper.tri(diag(ncol(pi_W)),diag=TRUE)
  NewData$unit <- rowSums(Ran_unif_W>cumul_W)
  
  beta_R_gender1 <- PostParameters[c("beta_R_gender1")]
  beta_R_gender2 <- PostParameters[c("beta_R_gender2[1]","beta_R_gender2[2]","beta_R_gender2[3]","beta_R_gender2[4]")]
  pi_R_gender <- beta_R_gender1 + beta_R_gender2[NewData$state] 
  pi_R_gender <- 1/(exp(-pi_R_gender)+1)
  pi_R_gender <- cbind(1-pi_R_gender,pi_R_gender)
  Ran_unif_R_gender <- runif(nrow(pi_R_gender))
  cumul_R_gender <- pi_R_gender%*%upper.tri(diag(ncol(pi_R_gender)),diag=TRUE)
  NewR <- data.frame(gender=rowSums(Ran_unif_R_gender>cumul_R_gender))
  
  beta_R_age1 <- PostParameters[c("beta_R_age1")]
  beta_R_age2 <- PostParameters[c("beta_R_age2[1]","beta_R_age2[2]","beta_R_age2[3]","beta_R_age2[4]")]
  beta_R_age3 <- PostParameters[c("beta_R_age3")]
  beta_R_age4 <- PostParameters[c("beta_R_age4")]
  pi_R_age <- beta_R_age1 + beta_R_age2[NewData$state] + beta_R_age3*NewData$gender + beta_R_age4*NewData$vote
  pi_R_age <- 1/(exp(-pi_R_age)+1)
  pi_R_age <- cbind(1-pi_R_age,pi_R_age)
  Ran_unif_R_age <- runif(nrow(pi_R_age^(1-NewR$gender)))
  cumul_R_age <- pi_R_age%*%upper.tri(diag(ncol(pi_R_age)),diag=TRUE)
  NewR$age <- rowSums(Ran_unif_R_age>cumul_R_age)
  
  beta_R_vote1 <- PostParameters[c("beta_R_vote1")]
  beta_R_vote2 <- PostParameters[c("beta_R_vote2[1]","beta_R_vote2[2]","beta_R_vote2[3]","beta_R_vote2[4]")]
  beta_R_vote3 <- PostParameters[c("beta_R_vote3[1]","beta_R_vote3[2]","beta_R_vote3[3]","beta_R_vote3[4]")]
  beta_R_vote4 <- PostParameters[c("beta_R_vote4")]
  pi_R_vote <- beta_R_vote1 + beta_R_vote2[NewData$state] + beta_R_vote3[NewData$age] + 
    beta_R_vote4*NewData$gender
  pi_R_vote <- 1/(exp(-pi_R_vote)+1)
  pi_R_vote <- cbind(1-pi_R_vote,pi_R_vote)
  Ran_unif_R_vote <- runif(nrow(pi_R_vote^(1-NewR$age)))
  cumul_R_vote <- pi_R_vote%*%upper.tri(diag(ncol(pi_R_vote)),diag=TRUE)
  NewR$vote <- rowSums(Ran_unif_R_vote>cumul_R_vote)
  
  #return(NewData)
  NewObservedData <- NewData[NewData$unit==0 & NewR$age==0 & NewR$gender==0 & NewR$vote==0,
                             c("state","age","gender","vote")]
  return(c(table(NewObservedData)/sum(table(NewObservedData))))
}

PostPred_NewData <- function(PostParameters,State){
  n <- length(State)
  NewData <- data.frame(state=State)
  
  beta_gender1 <- PostParameters[c("beta_gender1")]
  beta_gender2 <- PostParameters[c("beta_gender2[1]","beta_gender2[2]","beta_gender2[3]","beta_gender2[4]")]
  pi_gender <- beta_gender1 + beta_gender2[NewData$state]
  pi_gender <- 1/(exp(-pi_gender)+1)
  pi_gender <- cbind(1-pi_gender,pi_gender)
  Ran_unif_gender <- runif(nrow(pi_gender))
  cumul_gender <- pi_gender%*%upper.tri(diag(ncol(pi_gender)),diag=TRUE)
  NewData$gender <- rowSums(Ran_unif_gender>cumul_gender)
  
  pi_age <- cumm_pi_age <- matrix(0,ncol=4,nrow=n)
  beta_age1 <- PostParameters[c("beta_age1[1]","beta_age1[2]","beta_age1[3]")]
  beta_age2 <- PostParameters[c("beta_age2[1]","beta_age2[2]","beta_age2[3]","beta_age2[4]")]
  beta_age3 <- PostParameters[c("beta_age3")]
  cumm_pi_age[,1] <- beta_age1[1] + beta_age2[NewData$state] + beta_age3*NewData$gender
  cumm_pi_age[,1] <- 1/(exp(-cumm_pi_age[,1])+1)
  pi_age[,1] <- cumm_pi_age[,1]
  for(j in 2:3){
    cumm_pi_age[,j] <- beta_age1[j] + beta_age2[NewData$state] + beta_age3*NewData$gender
    cumm_pi_age[,j] <- 1/(exp(-cumm_pi_age[,j])+1)
    pi_age[,j] <- cumm_pi_age[,j] - cumm_pi_age[,j-1]
  }
  pi_age[,4] <- 1 - cumm_pi_age[,3]
  Ran_unif_age <- runif(nrow(pi_age))
  cumul_age <- pi_age%*%upper.tri(diag(ncol(pi_age)),diag=TRUE)
  NewData$age <- rowSums(Ran_unif_age>cumul_age) + 1L
  
  beta_vote1 <- PostParameters[c("beta_vote1")]
  beta_vote2 <- PostParameters[c("beta_vote2[1]","beta_vote2[2]","beta_vote2[3]","beta_vote2[4]")]
  beta_vote3 <- PostParameters[c("beta_vote3[1]","beta_vote3[2]","beta_vote3[3]","beta_vote3[4]")]
  beta_vote4 <- PostParameters[c("beta_vote4")]
  beta_vote5 <- matrix(0,ncol=4,nrow=4)
  beta_vote5[1,] <- PostParameters[c("beta_vote5[1,1]","beta_vote5[1,2]","beta_vote5[1,3]","beta_vote5[1,4]")]
  beta_vote5[2,] <- PostParameters[c("beta_vote5[2,1]","beta_vote5[2,2]","beta_vote5[2,3]","beta_vote5[2,4]")]
  beta_vote5[3,] <- PostParameters[c("beta_vote5[3,1]","beta_vote5[3,2]","beta_vote5[3,3]","beta_vote5[3,4]")]
  beta_vote5[4,] <- PostParameters[c("beta_vote5[4,1]","beta_vote5[4,2]","beta_vote5[4,3]","beta_vote5[4,4]")]
  pi_vote <- beta_vote1 + beta_vote2[NewData$state] + beta_vote3[NewData$age] + 
    beta_vote4*NewData$gender + c(unlist(lapply(c(1:n),function(x) beta_vote5[NewData$state[x],NewData$age[x]])))
  pi_vote <- 1/(exp(-pi_vote)+1)
  pi_vote <- cbind(1-pi_vote,pi_vote)
  Ran_unif_vote <- runif(nrow(pi_vote))
  cumul_vote <- pi_vote%*%upper.tri(diag(ncol(pi_vote)),diag=TRUE)
  NewData$vote <- rowSums(Ran_unif_vote>cumul_vote)
  
  beta_W1 <- PostParameters[c("beta_W1")]
  beta_W2 <- PostParameters[c("beta_W2[1]","beta_W2[2]","beta_W2[3]","beta_W2[4]")]
  beta_W3 <- PostParameters[c("beta_W3[1]","beta_W3[2]","beta_W3[3]","beta_W3[4]")]
  beta_W4 <- PostParameters[c("beta_W4")]
  pi_W <- beta_W1 + beta_W2[NewData$state] + beta_W3[NewData$age] + beta_W4*NewData$vote
  pi_W <- 1/(exp(-pi_W)+1)
  pi_W <- cbind(1-pi_W,pi_W)
  Ran_unif_W <- runif(nrow(pi_W))
  cumul_W <- pi_W%*%upper.tri(diag(ncol(pi_W)),diag=TRUE)
  NewData$unit <- rowSums(Ran_unif_W>cumul_W)
  
  beta_R_gender1 <- PostParameters[c("beta_R_gender1")]
  beta_R_gender2 <- PostParameters[c("beta_R_gender2[1]","beta_R_gender2[2]","beta_R_gender2[3]","beta_R_gender2[4]")]
  pi_R_gender <- beta_R_gender1 + beta_R_gender2[NewData$state] 
  pi_R_gender <- 1/(exp(-pi_R_gender)+1)
  pi_R_gender <- cbind(1-pi_R_gender,pi_R_gender)
  Ran_unif_R_gender <- runif(nrow(pi_R_gender))
  cumul_R_gender <- pi_R_gender%*%upper.tri(diag(ncol(pi_R_gender)),diag=TRUE)
  NewR <- data.frame(gender=rowSums(Ran_unif_R_gender>cumul_R_gender))
  
  beta_R_age1 <- PostParameters[c("beta_R_age1")]
  beta_R_age2 <- PostParameters[c("beta_R_age2[1]","beta_R_age2[2]","beta_R_age2[3]","beta_R_age2[4]")]
  beta_R_age3 <- PostParameters[c("beta_R_age3")]
  beta_R_age4 <- PostParameters[c("beta_R_age4")]
  pi_R_age <- beta_R_age1 + beta_R_age2[NewData$state] + beta_R_age3*NewData$gender + beta_R_age4*NewData$vote
  pi_R_age <- 1/(exp(-pi_R_age)+1)
  pi_R_age <- cbind(1-pi_R_age,pi_R_age)
  Ran_unif_R_age <- runif(nrow(pi_R_age^(1-NewR$gender)))
  cumul_R_age <- pi_R_age%*%upper.tri(diag(ncol(pi_R_age)),diag=TRUE)
  NewR$age <- rowSums(Ran_unif_R_age>cumul_R_age)
  
  beta_R_vote1 <- PostParameters[c("beta_R_vote1")]
  beta_R_vote2 <- PostParameters[c("beta_R_vote2[1]","beta_R_vote2[2]","beta_R_vote2[3]","beta_R_vote2[4]")]
  beta_R_vote3 <- PostParameters[c("beta_R_vote3[1]","beta_R_vote3[2]","beta_R_vote3[3]","beta_R_vote3[4]")]
  beta_R_vote4 <- PostParameters[c("beta_R_vote4")]
  pi_R_vote <- beta_R_vote1 + beta_R_vote2[NewData$state] + beta_R_vote3[NewData$age] + 
    beta_R_vote4*NewData$gender
  pi_R_vote <- 1/(exp(-pi_R_vote)+1)
  pi_R_vote <- cbind(1-pi_R_vote,pi_R_vote)
  Ran_unif_R_vote <- runif(nrow(pi_R_vote^(1-NewR$age)))
  cumul_R_vote <- pi_R_vote%*%upper.tri(diag(ncol(pi_R_vote)),diag=TRUE)
  NewR$vote <- rowSums(Ran_unif_R_vote>cumul_R_vote)
  
  return(list(NewData=NewData,NewR=NewR))
}


ProbVote_Posterior <- function(Model_mat_sub){
  VoteBySubgroups <- NULL; SubgroupsByVote = NULL; 
  ProbTurnout_NonRespAll = NULL; ProbTurnout_ItemNonRespVote = NULL
  for(j in 1:nrow(Model_mat_sub)){
    PostParameters_j <- Model_mat_sub[j,]
    
    # Vote given state, age and gender
    ExpGrid_st_ag_gd <- expand.grid(state=(1:4),gender=c(0,1),age=c(1:4))
    beta_vote1 <- PostParameters_j["beta_vote1"]
    beta_vote2 <- unlist(lapply(unique(ExpGrid_st_ag_gd$state),function(x) 
      PostParameters_j[paste0("beta_vote2[",x,"]")]))
    beta_vote3 <- unlist(lapply(unique(ExpGrid_st_ag_gd$age),function(x) 
      PostParameters_j[paste0("beta_vote3[",x,"]")]))
    beta_vote4 <- PostParameters_j["beta_vote4"]
    beta_vote5 <- matrix(0,ncol=4,nrow=4)
    beta_vote5[1,] <- PostParameters_j[c("beta_vote5[1,1]","beta_vote5[1,2]","beta_vote5[1,3]","beta_vote5[1,4]")]
    beta_vote5[2,] <- PostParameters_j[c("beta_vote5[2,1]","beta_vote5[2,2]","beta_vote5[2,3]","beta_vote5[2,4]")]
    beta_vote5[3,] <- PostParameters_j[c("beta_vote5[3,1]","beta_vote5[3,2]","beta_vote5[3,3]","beta_vote5[3,4]")]
    beta_vote5[4,] <- PostParameters_j[c("beta_vote5[4,1]","beta_vote5[4,2]","beta_vote5[4,3]","beta_vote5[4,4]")]
    Pr_v_giv_s_a_g <- apply(ExpGrid_st_ag_gd,1,function(x) 
      beta_vote1 + beta_vote2[x["state"]] + beta_vote3[x["age"]] + beta_vote4*x["gender"] + beta_vote5[x["state"],x["age"]])
    Pr_v_giv_s_a_g <- data.frame(Prob = 1/(exp(-Pr_v_giv_s_a_g)+1))
    cond_table <- cbind(Pr_v_giv_s_a_g,ExpGrid_st_ag_gd,data.frame(vote=1))
    vt_by_st_ag_gd <- cond_table
    cond_table_vt_0 <- cond_table; cond_table_vt_0$vote <- 0
    cond_table_vt_0$Prob = 1-cond_table_vt_0$Prob
    cond_table <- rbind(cond_table_vt_0,cond_table)
    
    
    # Vote and age given state and gender
    ExpGrid_st_gd <- expand.grid(state=(1:4),gender=c(0,1))
    Pr_a_giv_s_g <- cumm_a_giv_s_g <- matrix(0,ncol=4,nrow=8)
    beta_age1 <- unlist(lapply(c(1:3),function(x) 
      PostParameters_j[paste0("beta_age1[",x,"]")]))
    beta_age2 <- unlist(lapply(unique(ExpGrid_st_gd$state),function(x) 
      PostParameters_j[paste0("beta_age2[",x,"]")]))
    beta_age3 <- PostParameters_j["beta_age3"]
    cumm_a_giv_s_g[,1] <- beta_age1[1] + beta_age2[ExpGrid_st_gd$state] + beta_age3*ExpGrid_st_gd$gender
    cumm_a_giv_s_g[,1] <- 1/(exp(-cumm_a_giv_s_g[,1])+1)
    Pr_a_giv_s_g[,1] <- cumm_a_giv_s_g[,1]
    for(j in 2:3){
      cumm_a_giv_s_g[,j] <- beta_age1[j] + beta_age2[ExpGrid_st_gd$state] + beta_age3*ExpGrid_st_gd$gender
      cumm_a_giv_s_g[,j] <- 1/(exp(-cumm_a_giv_s_g[,j])+1)
      Pr_a_giv_s_g[,j] <- cumm_a_giv_s_g[,j] - cumm_a_giv_s_g[,j-1]
    }
    Pr_a_giv_s_g[,4] <- 1 - cumm_a_giv_s_g[,3]
    for(ag in 1:4){
      cond_table[cond_table$age==ag,"Prob"] <- 
        cond_table[cond_table$age==ag,"Prob"] * Pr_a_giv_s_g[,ag]
    }
    vt_by_st_gd <- aggregate(cond_table$Prob,FUN=sum,
                             by=list(state=cond_table$state,gender=cond_table$gender,vote=cond_table$vote))
    
    
    # Vote, gender and age given state
    ExpGrid_st <- expand.grid(state=(1:4))
    beta_gender1 <- PostParameters_j["beta_gender1"]
    beta_gender2 <- unlist(lapply(unique(ExpGrid_st$state),function(x) 
      PostParameters_j[paste0("beta_gender2[",x,"]")]))
    Pr_g_giv_s <- apply(ExpGrid_st,1,function(x) beta_gender1 + beta_gender2[x["state"]])
    Pr_g_giv_s <- 1/(exp(-Pr_g_giv_s)+1)
    cond_table[cond_table$gender==1,"Prob"] <- 
      cond_table$Prob[cond_table$gender==1]*rep(Pr_g_giv_s,4)
    cond_table[cond_table$gender==0,"Prob"] <- 
      cond_table$Prob[cond_table$gender==0]*(1-rep(Pr_g_giv_s,4))
    
    
    # Calculate vote by subgroups
    # vote by state
    vt_by_st <- aggregate(cond_table$Prob,FUN=sum,
                          by=list(state=cond_table$state,vote=cond_table$vote))
    VoteBySubgroups_j <- matrix(vt_by_st$x[vt_by_st$vote==1],nrow=1)
    colnames(VoteBySubgroups_j) <- c("FL","GA","NC","SC")
    # vote by gender and state
    VoteBySubgroups_j <- rbind(VoteBySubgroups_j,matrix(vt_by_st_gd$x[vt_by_st_gd$vote==1],ncol=4,byrow=TRUE))
    # vote by age and state
    vt_by_st_ag <- aggregate(cond_table$Prob,FUN=sum,
                             by=list(state=cond_table$state,age=cond_table$age,vote=cond_table$vote))
    ag_cond_st <- aggregate(cond_table$Prob,FUN=sum,
                            by=list(state=cond_table$state,age=cond_table$age))
    for(k in 1:nrow(vt_by_st_ag)){
      vt_by_st_ag$x[k] <- vt_by_st_ag$x[k]/ag_cond_st$x[is.element(ag_cond_st$state,vt_by_st_ag$state[k]) &
                                                          is.element(ag_cond_st$age,vt_by_st_ag$age[k])]
    }
    VoteBySubgroups_j <- rbind(VoteBySubgroups_j,matrix(vt_by_st_ag$x[vt_by_st_ag$vote==1],ncol=4,byrow=TRUE))
    # vote by gender, age and state
    vt_by_st_ag_gd <- vt_by_st_ag_gd[order(vt_by_st_ag_gd$gender,vt_by_st_ag_gd$age,vt_by_st_ag_gd$state),]
    VoteBySubgroups_j <- rbind(VoteBySubgroups_j,matrix(vt_by_st_ag_gd$Prob[vt_by_st_ag_gd$vote==1],ncol=4,byrow=TRUE))
    
    
    # Now calculate voter composition
    ag_gd_by_st_vt1 <- cond_table[cond_table$vote==1,]
    vt1_cond_st <- vt_by_st[vt_by_st$vote==1,]
    for(k in unique(vt1_cond_st$state)){
      ag_gd_by_st_vt1$Prob[ag_gd_by_st_vt1$state==k] <- 
        ag_gd_by_st_vt1$Prob[ag_gd_by_st_vt1$state==k]/vt1_cond_st$x[vt1_cond_st$state==k]
    }
    # gender by state and vote=1
    gd_by_st_vt1 <- aggregate(ag_gd_by_st_vt1$Prob,FUN=sum,
                          by=list(state=ag_gd_by_st_vt1$state,gender=ag_gd_by_st_vt1$gender))
    SubgroupsByVote_j <- matrix(gd_by_st_vt1$x,ncol=4,byrow=TRUE)
    colnames(SubgroupsByVote_j) <- c("FL","GA","NC","SC")
    # age by state and vote=1
    ag_by_st_vt1 <- aggregate(ag_gd_by_st_vt1$Prob,FUN=sum,
                              by=list(state=ag_gd_by_st_vt1$state,age=ag_gd_by_st_vt1$age))
    SubgroupsByVote_j <- rbind(SubgroupsByVote_j,matrix(ag_by_st_vt1$x,ncol=4,byrow=TRUE))
    # gender, age by state and vote=1
    ag_gd_by_st_vt1 <- ag_gd_by_st_vt1[order(ag_gd_by_st_vt1$gender,ag_gd_by_st_vt1$age,ag_gd_by_st_vt1$state),]
    SubgroupsByVote_j <- rbind(SubgroupsByVote_j,matrix(ag_gd_by_st_vt1$Prob,ncol=4,byrow=TRUE))
    
    
    # Posterior predicted turnout among unit nonrespondents
    # U given state, age, gender and vote
    ExpGrid_st_ag <- expand.grid(state=(1:4),age=c(1:4),vote=c(0:1))
    beta_W1 <- PostParameters_j["beta_W1"]
    beta_W2 <- unlist(lapply(unique(ExpGrid_st_ag$state),function(x) 
      PostParameters_j[paste0("beta_W2[",x,"]")]))
    beta_W3 <- unlist(lapply(unique(ExpGrid_st_ag$age),function(x) 
      PostParameters_j[paste0("beta_W3[",x,"]")]))
    beta_W4 <- PostParameters_j["beta_W4"]
    Pr_u_giv_s_a_g_v <- apply(ExpGrid_st_ag,1,function(x) beta_W1 + beta_W2[x["state"]] + beta_W3[x["age"]] + beta_W4*x["vote"])
    Pr_u_giv_s_a_g_v <- data.frame(Prob = 1/(exp(-Pr_u_giv_s_a_g_v)+1))
    u_by_st_ag_gd_vt <- cbind(Pr_u_giv_s_a_g_v,ExpGrid_st_ag,data.frame(unit=1))
    cond_table_with_u <- cond_table
    for(k in 1:nrow(cond_table_with_u)){
      cond_table_with_u$Prob[k] <- cond_table_with_u$Prob[k]*
        u_by_st_ag_gd_vt$Prob[is.element(u_by_st_ag_gd_vt$state,cond_table_with_u$state[k]) &
                                is.element(u_by_st_ag_gd_vt$age,cond_table_with_u$age[k]) &
                                is.element(u_by_st_ag_gd_vt$vote,cond_table_with_u$vote[k])]
    }
    cond_table_with_u <- cbind(cond_table_with_u,data.frame(unit=1))
    u1_v1_by_st <- aggregate(cond_table_with_u$Prob,FUN=sum,
              by=list(state=cond_table_with_u$state,vote=cond_table_with_u$vote))
    u1_by_st <- aggregate(u1_v1_by_st$x,FUN=sum,
                          by=list(state=u1_v1_by_st$state))
    ProbTurnout_NonRespAll_j <- u1_v1_by_st$x[u1_v1_by_st$vote==1]/u1_by_st$x
    
    
    # Finally, posterior predicted turnout among item nonrespondents
    # R_vote given state, age, gender and vote
    ExpGrid_st_ag_gd_vt <- expand.grid(state=(1:4),age=c(1:4),gender=c(0,1))
    beta_R_vote1 <- PostParameters_j["beta_R_vote1"]
    beta_R_vote2 <- unlist(lapply(unique(ExpGrid_st_ag_gd_vt$state),function(x) 
      PostParameters_j[paste0("beta_R_vote2[",x,"]")]))
    beta_R_vote3 <- unlist(lapply(unique(ExpGrid_st_ag_gd_vt$age),function(x) 
      PostParameters_j[paste0("beta_R_vote3[",x,"]")]))
    beta_R_vote4 <- PostParameters_j["beta_R_vote4"]
    Pr_r_vote_giv_s_a_g_v <- apply(ExpGrid_st_ag_gd_vt,1,function(x) beta_R_vote1 + beta_R_vote2[x["state"]] + 
                                     beta_R_vote3[x["age"]] + beta_R_vote4*x["gender"])
    Pr_r_vote_giv_s_a_g_v <- data.frame(Prob = 1/(exp(-Pr_r_vote_giv_s_a_g_v)+1))
    r_vote_by_st_ag_gd_vt <- cbind(Pr_r_vote_giv_s_a_g_v,ExpGrid_st_ag_gd_vt,data.frame(R_vote=1))
    cond_table_with_r_vote <- cond_table
    for(k in 1:nrow(cond_table_with_r_vote)){
      cond_table_with_r_vote$Prob[k] <- cond_table_with_r_vote$Prob[k]*
        r_vote_by_st_ag_gd_vt$Prob[is.element(r_vote_by_st_ag_gd_vt$state,cond_table_with_r_vote$state[k]) &
                                     is.element(r_vote_by_st_ag_gd_vt$age,cond_table_with_r_vote$age[k]) &
                                     is.element(r_vote_by_st_ag_gd_vt$gender,cond_table_with_r_vote$gender[k])]
    }
    cond_table_with_r_vote <- cbind(cond_table_with_r_vote,data.frame(R_vote=1))
    r_vote1_v1_by_st <- aggregate(cond_table_with_r_vote$Prob,FUN=sum,
                                  by=list(state=cond_table_with_r_vote$state,vote=cond_table_with_r_vote$vote))
    r_vote1_by_st <- aggregate(r_vote1_v1_by_st$x,FUN=sum,
                               by=list(state=r_vote1_v1_by_st$state))
    ProbTurnout_ItemNonRespVote_j <- r_vote1_v1_by_st$x[r_vote1_v1_by_st$vote==1]/r_vote1_by_st$x
    
    
    VoteBySubgroups <- cbind(VoteBySubgroups,c(VoteBySubgroups_j)) 
    #use matrix(VoteBySubgroups,ncol=4); colnames(VoteBySubgroups) <- c("FL","GA","NC","SC") to recover order
    SubgroupsByVote <- cbind(SubgroupsByVote,c(SubgroupsByVote_j))
    #use matrix(SubgroupsByVote,ncol=4); colnames(SubgroupsByVote) <- c("FL","GA","NC","SC") to recover order
    ProbTurnout_NonRespAll <- rbind(ProbTurnout_NonRespAll,c(ProbTurnout_NonRespAll_j))
    ProbTurnout_ItemNonRespVote <- rbind(ProbTurnout_ItemNonRespVote,c(ProbTurnout_ItemNonRespVote_j))
  }
  
  return(list(VoteBySubgroups=VoteBySubgroups,
              SubgroupsByVote=SubgroupsByVote,
              ProbTurnout_NonRespAll=ProbTurnout_NonRespAll,
              ProbTurnout_ItemNonRespVote=ProbTurnout_ItemNonRespVote))
}




###### 3: Load Data
Data <- read.csv("CPSData.csv",header=T,row.names = 1)
#Data <- Data %>% sample_frac(0.25)
#head(Data) #4 variables: state (4 levels), age (4 levels), gender (2 levels), vote (2 levels)
Data$gender <- Data$gender - 1 #Recode to 0 and 1
Data$vote <- Data$vote - 1 #Recode to 0 and 1
Data$state[Data$state==12] <- 1 #Recode FL to 1
Data$state[Data$state==13] <- 2 #Recode GA to 2
Data$state[Data$state==37] <- 3 #Recode NC to 3
Data$state[Data$state==45] <- 4 #Recode SC to 4
Data$age <- Data$age + 1 #Recode to 1 to 4
table(Data$state,useNA = "ifany")/nrow(Data) #No NA in state.
table(Data$vote,Data$unit,useNA = "ifany")/nrow(Data)
table(Data$age,Data$unit,useNA = "ifany")/nrow(Data)
table(Data$gender,Data$unit,useNA = "ifany")/nrow(Data)
table(Data$unit,useNA = "ifany")/nrow(Data)

R <- data.frame(state=ifelse(is.na(Data$state),1,0))
R$age <- ifelse(is.na(Data$age),1,0)
R$gender <- ifelse(is.na(Data$gender),1,0)
R$vote <- ifelse(is.na(Data$vote),1,0)
R[Data$unit==1,c("age","gender","vote")] <- NA


###### 4: Augment the Data with marginal voter information and age margins
###### Vote margin --- Florida = 62.8%; Georgia = 59.0%; North Carolina = 64.8%; South Carolina = 56.3%
###### Observed vote prop. --- Florida = 75.2%; Georgia = 73.4%; North Carolina = 77.4%; South Carolina = 72.6%
#Age information from 2010 census remarginalized
#FL:::: 18-29 = 19.67(15.5), 30-49 = 33.50(26.4), 50-69 = 31.22(24.6), 70+ = 15.61(12.3)
#GA:::: 18-29 = 22.88(17), 30-49 = 38.63(28.7), 50-69 = 29.07(21.6), 70+ = 9.42(7)
#NC:::: 18-29 = 21.64(16.4), 30-49 = 36.54(27.7), 50-69 = 30.47(23.1), 70+ = 11.34(8.6)
#SC:::: 18-29 = 22.03(16.9), 30-49 = 34.41(26.4), 50-69 = 31.94(24.5), 70+ = 11.60(8.9)
Multiplier <- 3
n_i <- (as.data.frame(table(Data$state)))$Freq
n <- sum(n_i)
n_i_0 <- Multiplier*n_i
n_0 <- sum(n_i_0)
state_levels <- c(1:4); state_vote_margins <- c(0.628,0.59,0.648,0.563)
state_age_margins <- list(FL=c(0.1967,0.3350,0.3122,0.1561),
                          GA=c(0.2288,0.3863,0.2907,0.0942),
                          NC=c(0.2164,0.3654,0.3047,0.1134),
                          SC=c(0.2203,0.3441,0.3194,0.1160))

Aug_state <- NULL
Aug_vote <- NULL
Aug_age <- NULL
for(i in 1:length(state_levels)){
  Aug_state <- c(Aug_state,rep(state_levels[i],(n_i_0[i]*2)))
  Aug_vote <- c(Aug_vote,c(rbinom((n_i_0[i]),1,state_vote_margins[i]),rep(NA,n_i_0[i])))
  Aug_age <- c(Aug_age,c(rep(NA,n_i_0[i]),sample(c(1:4),size=n_i_0[i],replace=TRUE,prob=c(state_age_margins[[i]]))))
}
Aug_gender <- rep(NA,length(Aug_state)); Aug_unit <- rep(NA,length(Aug_state))
Aug_Data <- cbind(Aug_state,Aug_age,Aug_gender,Aug_vote,Aug_unit)
colnames(Aug_Data) <- c("state","age","gender","vote","unit")
Aug_R <- Aug_Data[,c("state","age","gender","vote")]
Aug_R[] <- NA
Aug_Data <- rbind(Data[,c("state","age","gender","vote","unit")],Aug_Data)
Aug_R <- rbind(R,Aug_R)



###### 5: Gibbs Sampler
### Gibbs Sampler
dataList <- list(
  state = Aug_Data$state,
  age = Aug_Data$age,
  gender = Aug_Data$gender,
  vote = Aug_Data$vote,
  #R_state = Aug_R$state,
  R_age = Aug_R$age,
  R_gender = Aug_R$gender,
  R_vote = Aug_R$vote,
  W = Aug_Data$unit,
  N = nrow(Aug_Data),
  n = n
)

JagsModel = " model {
# Likelihood:
for(i in 1:N){
#logit model for gender
gender[i] ~ dbern(pi_gender[i])
logit(pi_gender[i]) = beta_gender1 + beta_gender2[state[i]]

#cummulative logit model for age
age[i] ~ dcat(pi_age[i,])
logit(cumm_pi_age[i,1]) = beta_age1[1] + beta_age2[state[i]] + beta_age3*gender[i]
pi_age[i,1] <- cumm_pi_age[i,1]
for(j in 2:3){
logit(cumm_pi_age[i,j]) = beta_age1[j] + beta_age2[state[i]] + beta_age3*gender[i]
pi_age[i,j] <- cumm_pi_age[i,j] - cumm_pi_age[i,j-1]
}
pi_age[i,4] <- 1 - cumm_pi_age[i,3]

#logit model for vote
vote[i] ~ dbern(pi_vote[i])
logit(pi_vote[i]) = beta_vote1 + beta_vote2[state[i]] + beta_vote3[age[i]] + beta_vote4*gender[i]  +
    beta_vote5[state[i],age[i]]

#logit model for unit nonresponse
W[i] ~ dbern(pi_W[i])
logit(pi_W[i]) = beta_W1 + beta_W2[state[i]] + beta_W3[age[i]] + beta_W4*vote[i]

#logit model for the item nonresponse indicator for gender
R_gender[i] ~ dbern(pi_R_gender[i])
logit(pi_R_gender[i]) = beta_R_gender1 + beta_R_gender2[state[i]]

#logit model for the item nonresponse indicator for age
R_age[i] ~ dbern(pi_R_age[i]^(1-R_gender[i]))
logit(pi_R_age[i]) = beta_R_age1 + beta_R_age2[state[i]] + beta_R_age3*gender[i] + beta_R_age4*vote[i]

#logit model for the item nonresponse indicator for vote
R_vote[i] ~ dbern(pi_R_vote[i]^(1-R_age[i]))
logit(pi_R_vote[i]) = beta_R_vote1 + beta_R_vote2[state[i]] + beta_R_vote3[age[i]] + 
  beta_R_vote4*gender[i]
}

# Priors:
beta_gender1 ~ dnorm(0,0.01)
for(a in 1:3){
beta_age0[a] ~ dnorm(0,0.01)
}
beta_age1 <- sort(beta_age0)
beta_age3 ~ dnorm(0,0.01)
beta_vote1 ~ dnorm(0,0.01)
beta_vote4 ~ dnorm(0,0.01)
beta_W1 ~ dnorm(0,0.01)
beta_W4 ~ dnorm(0,0.01)
beta_R_gender1 ~ dnorm(0,0.01)
beta_R_age1 ~ dnorm(0,0.01)
beta_R_age3 ~ dnorm(0,0.01)
beta_R_age4 ~ dnorm(0,0.01)
beta_R_vote1 ~ dnorm(0,0.01)
beta_R_vote4 ~ dnorm(0,0.01)
for(b in 2:4){
beta_gender2[b] ~ dnorm(0,0.01)
beta_age2[b] ~ dnorm(0,0.01)
beta_vote2[b] ~ dnorm(0,0.01)
beta_vote3[b] ~ dnorm(0,0.01)
for(c in 2:4){
      beta_vote5[b,c] ~ dnorm(0,0.01)
}
beta_W2[b] ~ dnorm(0,0.01)
beta_W3[b] ~ dnorm(0,0.01)
beta_R_gender2[b] ~ dnorm(0,0.01)
beta_R_age2[b] ~ dnorm(0,0.01)
beta_R_vote2[b] ~ dnorm(0,0.01)
beta_R_vote3[b] ~ dnorm(0,0.01)
}
beta_gender2[1] <- 0
beta_age2[1] <- 0
beta_vote2[1] <- 0
beta_vote3[1] <- 0
beta_vote5[1,1:4] <- c(0,0,0,0)
beta_vote5[2:4,1] <- c(0,0,0)
beta_W2[1] <- 0
beta_W3[1] <- 0
beta_R_gender2[1] <- 0
beta_R_age2[1] <- 0
beta_R_vote2[1] <- 0
beta_R_vote3[1] <- 0


ImpAge <- age[1:n]
ImpGender <- gender[1:n]
ImpVote <- vote[1:n]
} "
inits <- list("beta_age0" = c(-0.5, 0, 0.5))
Model <- run.jags(JagsModel,monitor = c("beta_gender1","beta_gender2",
                                        "beta_age1","beta_age2","beta_age3",
                                        "beta_vote1","beta_vote2","beta_vote3",
                                        "beta_vote4","beta_vote5",
                                        "beta_W1","beta_W2","beta_W3","beta_W4",
                                        "beta_R_gender1","beta_R_gender2",
                                        "beta_R_age1","beta_R_age2",
                                        "beta_R_age3","beta_R_age4",
                                        "beta_R_vote1","beta_R_vote2",
                                        "beta_R_vote3","beta_R_vote4",
                                        "ImpAge","ImpGender","ImpVote"),
                  inits=inits,n.chains = 1, data = dataList,burnin = 5000, 
                  sample = 5000,summarise=F,thin=1)

Model_mcmc <- as.mcmc.list(Model)
Model_mat <- as.matrix(Model_mcmc)

ImpDataNames <- c(unlist(lapply(c(1:n),function(x) paste0("ImpAge[",x,"]"))),
                  unlist(lapply(c(1:n),function(x) paste0("ImpGender[",x,"]"))),
                  unlist(lapply(c(1:n),function(x) paste0("ImpVote[",x,"]"))))
Model_mat_sub <- Model_mat[,!is.element(colnames(Model_mat),ImpDataNames)]
PostParameters <- Post_Summary(Model_mat_sub)
PostParameters
for(j in 1:ncol(Model_mat_sub)){
  plot(Model_mat_sub[,j], type = 'l',ylab=paste(colnames(Model_mat_sub)[j]))
}
#Model_mat_sub <- t(Model_mat_sub)


###### 6: Model check - generate data from fitted model and compare respondents to observed data
PredObservedPE <- apply(Model_mat_sub,1,function(x) PostPred_ContTable(x,Data$state))
ObservedData <- na.omit(Data)[,c("state","age","gender","vote")]
ObservedPE <- c(table(ObservedData)/sum(table(ObservedData)))
PredCI <- t(apply(PredObservedPE,1,function(x) quantile(x,probs = c(0.025, 0.975))))
PredPE <- apply(PredObservedPE,1,mean)
PredCI_check <- apply(cbind(PredCI,ObservedPE),1,function(x) ifelse((x[3]>=x[1] & x[3]<=x[2]),1,0))
mean(PredCI_check)
sum(PredCI_check)

#make CI plots to indicate posterior predictive checks
PredCI_col <- ifelse(PredCI_check==1,"lightblue3","red4")
PredCI_lwd <- ifelse(PredCI_check==1,1,2)

#png("Figures/PosteriorPredictiveCheck_Model2_NewData.png",pointsize=12,width = 8, height = 6,bg="white",units="in",res=150)
postscript("Figures/PosteriorPredictiveCheck_NewData_MD-U.eps",
           width = 6.5, height = 8, horizontal = FALSE, onefile = FALSE)
plot(ObservedPE, pch=4, ylim=range(pretty(c(PredCI[,1], PredCI[,2]))),
     xlab='Index', ylab='Joint probabilities', las=1,col="orange4",
     main="")
segments(seq_len(length(PredPE)), PredCI[,1], y1=PredCI[,2], lend=1,
         lwd=PredCI_lwd,col=PredCI_col)
points(PredCI[,1], pch="-", bg=PredCI_col); points(PredCI[,2], pch="-", bg=PredCI_col)
legend("topleft", inset=.05, bty="n",
       legend=c("Intervals containing observed estimates",
                "Intervals NOT containing observed estimates","Observed data point estimates"),
       lwd=c(1,2,1), lty=c(1,1,NA),pch=c(NA,NA,4), col=c("lightblue3","red4",'orange4'))
dev.off()


#Note intervals in Red
ExpGrid_temp <- expand.grid(State=c("FL","GA","NC","SC"),
                            Age=c("<30","30-49","50-69","70+"),
                            Gender=c("M","F"),
                            Vote=c("No","Yes"))
ExpGrid_temp <- cbind(ExpGrid_temp,
                      ObservedSampleSize=as.data.frame(table(ObservedData))$Freq,
                      ObservedProbEstimates=round(as.data.frame(table(ObservedData)/sum(table(ObservedData)))$Freq,4))
ExpGrid_temp[PredCI_check==0,]
#State   Age Gender Vote ObservedSampleSize ObservedProbEstimates
#1     FL   <30      M   No                125                0.0166
#14    GA   70+      M   No                 12                0.0016
#20    SC   <30      F   No                 28                0.0037
#31    NC   70+      F   No                 29                0.0038
#60    SC 50-69      F  Yes                214                0.0284

#plot(PredPE, pch=4, ylim=range(pretty(c(PredCI[,1], PredCI[,2]))),
#     xlab='', ylab='Joint probabilities', las=1,col="darkblue",
#     main="Joint contigency table for respondents (posterior predicted vs. observed data)",
#     panel.first=plot(ObservedPE ~ factor(seq_len(length(ObservedPE))), add=TRUE,
#                      xlab='', ylab='', axes=FALSE, border='red4', medlwd=3))



###### 7: Vote turnout by subgroups
VoteTurnoutPosterior <- ProbVote_Posterior(Model_mat_sub)
Results <- NULL
Results$VoteBySubgroups <- round(matrix(rowMeans(VoteTurnoutPosterior$VoteBySubgroups),ncol=4),2)
Results$VoteBySubgroupsSE <- round(matrix(apply(VoteTurnoutPosterior$VoteBySubgroups,1,sd),ncol=4),2)
Results$SubgroupsByVote <- round(matrix(rowMeans(VoteTurnoutPosterior$SubgroupsByVote),ncol=4),2)
Results$ProbTurnout_NonRespAll <- VoteTurnoutPosterior$ProbTurnout_NonRespAll
Results$ProbTurnout_ItemNonRespVote <- VoteTurnoutPosterior$ProbTurnout_ItemNonRespVote

colnames(Results$VoteBySubgroups) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroups) <- c("Full","M","F","<30","30-49","50-69","70+",
                                            "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                            "<30(F)","30-49(F)","50-69(F)","70+(F)")
colnames(Results$VoteBySubgroupsSE) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroupsSE) <- c("Full","M","F","<30","30-49","50-69","70+",
                                         "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                         "<30(F)","30-49(F)","50-69(F)","70+(F)")
colnames(Results$SubgroupsByVote) <- c("FL","GA","NC","SC")
rownames(Results$SubgroupsByVote) <- c("M","F","<30","30-49","50-69","70+",
                                       "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                       "<30(F)","30-49(F)","50-69(F)","70+(F)")
colnames(Results$ProbTurnout_NonRespAll) <- c("FL","GA","NC","SC")
colnames(Results$ProbTurnout_ItemNonRespVote) <- c("FL","GA","NC","SC")


xtable(Results$VoteBySubgroups)
xtable(Results$VoteBySubgroupsSE)


Results$VoteBySubgroupsLB <- round(matrix(apply(VoteTurnoutPosterior$VoteBySubgroups,1,
                                                function(x) quantile(x,probs=c(0.025))),ncol=4),2)
colnames(Results$VoteBySubgroupsLB) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroupsLB) <- c("Full","M","F","<30","30-49","50-69","70+",
                                         "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                         "<30(F)","30-49(F)","50-69(F)","70+(F)")
Results$VoteBySubgroupsUB <- round(matrix(apply(VoteTurnoutPosterior$VoteBySubgroups,1,
                                                function(x) quantile(x,probs=c(0.975))),ncol=4),2)
colnames(Results$VoteBySubgroupsUB) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroupsUB) <- c("Full","M","F","<30","30-49","50-69","70+",
                                         "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                         "<30(F)","30-49(F)","50-69(F)","70+(F)")
#Results$VoteBySubgroupsLB
#Results$VoteBySubgroupsUB

cbind(Results$VoteBySubgroupsLB[,"FL"],Results$VoteBySubgroupsUB[,"FL"])
cbind(Results$VoteBySubgroupsLB[,"GA"],Results$VoteBySubgroupsUB[,"GA"])
cbind(Results$VoteBySubgroupsLB[,"NC"],Results$VoteBySubgroupsUB[,"NC"])
cbind(Results$VoteBySubgroupsLB[,"SC"],Results$VoteBySubgroupsUB[,"SC"])



CatalistVoterComposition <- as.data.frame(matrix(c(0.45,0.44,0.45,0.43,0.55,0.56,0.55,0.57,
                                                   0.13,0.14,0.15,0.13,0.29,0.36,0.34,0.32,
                                                   0.38,0.38,0.37,0.40,0.20,0.13,0.14,0.16,
                                                   0.06,0.06,0.07,0.05,0.13,0.15,0.15,0.14,
                                                   0.17,0.17,0.17,0.18,0.09,0.06,0.06,0.07,
                                                   0.08,0.08,0.09,0.08,0.16,0.20,0.19,0.18,
                                                   0.21,0.20,0.20,0.22,0.11,0.07,0.08,0.09),
                                                 byrow=TRUE,ncol=4))
colnames(CatalistVoterComposition) <- c("FL","GA","NC","SC")
rownames(CatalistVoterComposition) <- c("M","F","<30","30-49","50-69","70+",
                                        "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                        "<30(F)","30-49(F)","50-69(F)","70+(F)")

Deviation <- Results$SubgroupsByVote - CatalistVoterComposition
Deviation
Deviation_DF <- data.frame(Deviation=c(as.matrix(Deviation)),
                           State=rep(colnames(Deviation),each=nrow(Deviation)))


#png("Figures/DeviationInVoterCompositionEstimates_PostEst_Model2_NewData.png",pointsize=11,width = 13, height = 7,bg="white",units="in",res=150)
#plot_ly(Deviation_DF, y = ~Deviation,
#        color = Deviation_DF$State,
#        alpha = 0.1, boxpoints = "suspectedoutliers") %>% 
#  add_boxplot(y = Deviation$FL, name = "FL", boxpoints = 'outliers',
#              marker = list(color = 'rgb(7,40,89)'),line = list(color = 'rgb(7,40,89)')) %>%
#  add_boxplot(y = Deviation$GA, name = "GA", boxpoints = 'outliers',
#              marker = list(color = 'rgb(9,56,125)'),line = list(color = 'rgb(9,56,125)')) %>%
#  add_boxplot(y = Deviation$NC, name = "NC", boxpoints = 'outliers',
#              marker = list(color = 'rgb(8,81,156)'),line = list(color = 'rgb(8,81,156)')) %>%
#  add_boxplot(y = Deviation$SC, name = "SC", boxpoints = 'outliers',
#              marker = list(color = 'rgb(107,174,214)'),line = list(color = 'rgb(107,174,214)')) %>%
#  layout(showlegend = FALSE, yaxis = list(title = "",range = c(-0.1, 0.1)))
#dev.off()


#png("Figures/DeviationInVoterCompositionEstimates_PostEst_Model2_NewData.png",pointsize=8,width = 6, height = 4,bg="white",units="in",res=150)
postscript("Figures/DeviationInVoterCompositionEstimates_PostEst_NewData_MD-U.eps",
           width = 6.5, height = 3.5, horizontal = FALSE, onefile = FALSE)
ggplot(Deviation_DF, aes(y = Deviation, x = State)) +
  geom_boxplot(colour = c("#072859","#09387D","#09387D","#6BAED6")) +
  scale_y_continuous(name = "Deviations",breaks = seq(-0.1, 0.1, 0.05),limits=c(-0.1,0.1)) +
  scale_x_discrete(name = "State") +
  geom_point(shape = 5,color = "orange4") +
  theme_classic() +
  geom_hline(yintercept = 0,lty=2,col="grey50")
dev.off()


#png("Figures/VoterTurnoutForUnitNonrespondents_Boxplot_PostEst_Model2_NewData.png",pointsize=11,width = 13, height = 7,bg="white",units="in",res=150)
#plot_ly(type = 'box') %>% 
#  add_boxplot(y = Results$ProbTurnout_NonRespAll[,"FL"], name = "FL", boxpoints = 'outliers',
#              marker = list(color = 'rgb(7,40,89)'),line = list(color = 'rgb(7,40,89)')) %>%
#  add_boxplot(y = Results$ProbTurnout_NonRespAll[,"GA"], name = "GA", boxpoints = 'outliers',
#              marker = list(color = 'rgb(9,56,125)'),line = list(color = 'rgb(9,56,125)')) %>%
#  add_boxplot(y = Results$ProbTurnout_NonRespAll[,"NC"], name = "NC", boxpoints = 'outliers',
#              marker = list(color = 'rgb(8,81,156)'),line = list(color = 'rgb(8,81,156)')) %>%
#  add_boxplot(y = Results$ProbTurnout_NonRespAll[,"SC"], name = "SC", boxpoints = 'outliers',
#              marker = list(color = 'rgb(107,174,214)'),line = list(color = 'rgb(107,174,214)')) %>%
#  layout(showlegend = FALSE, yaxis = list(title = ""))
  #layout(showlegend = FALSE, yaxis = list(title = "",range = c(0.39, 0.71)))
#dev.off()


PostPredTurnout <- data.frame(State=rep(c("FL","GA","NC","SC"),each=nrow(Results$ProbTurnout_NonRespAll)), 
                              Turnout = c(Results$ProbTurnout_NonRespAll))
#png("Figures/VoterTurnoutForUnitNonrespondents_Violin_PostEst_Model2_NewData.png",pointsize=11,width = 13, height = 7,bg="white",units="in",res=150)
#PostPredTurnout %>%
#  plot_ly(x = ~State,y = ~Turnout,split = ~State,type = 'violin',color=~State,
#    box = list(visible = T),meanline = list(visible = T),
#    colors = c("#072859","#09387D","#08519C","#6BAED6")) %>% 
#  layout(xaxis = list(title = "State"),yaxis = list(title = "Turnout",zeroline = T,range = c(0.05, 0.3)),showlegend = FALSE)
#dev.off()


postscript("Figures/VoterTurnoutForUnitNonrespondents_Violin_PostEst_NewData_MD-U.eps",
           width = 6.5, height = 3.5, horizontal = FALSE, onefile = FALSE)
ggplot(PostPredTurnout, aes(y = Turnout, x = State)) +
  geom_violin(aes(color=State, fill=State),show.legend = FALSE) +
  #geom_violin(aes(color=State),show.legend = FALSE) +
  geom_boxplot(aes(color=State),fill="ivory2",width = 0.2,show.legend = FALSE) +
  #scale_fill_manual(values=c("#072859","#09387D","#08519C","#6BAED6")) +
  #scale_fill_manual(values=c("#01525c","#026b78","#013940","#038494")) +
  scale_fill_manual(values=c("snow3","snow2","snow4","snow1")) +
  scale_color_manual(values=c("tomato3","tomato2","tomato4","tomato1")) +
  #scale_color_grey() +
  scale_y_continuous(name = "Turnout",breaks = seq(0, 0.7, 0.1),limits=c(0,0.7)) +
  scale_x_discrete(name = "State") +
  theme_classic() #+
  #geom_hline(yintercept = c(by(PostPredTurnout$Turnout,PostPredTurnout$State,median)),lty=2,col="grey50")
dev.off()


PostPredTurnout_Vote <- data.frame(State=rep(c("FL","GA","NC","SC"),each=nrow(Results$ProbTurnout_ItemNonRespVote)), 
                                   Turnout = c(Results$ProbTurnout_ItemNonRespVote))

postscript("Figures/VoterTurnoutForItemNonrespondentsVote_Violin_PostEst_NewData_MD-U.eps",
           width = 6.5, height = 3.5, horizontal = FALSE, onefile = FALSE)
ggplot(PostPredTurnout_Vote, aes(y = Turnout, x = State)) +
  geom_violin(aes(color=State, fill=State),show.legend = FALSE) +
  #geom_violin(aes(color=State),show.legend = FALSE) +
  geom_boxplot(aes(color=State),fill="ivory2",width = 0.2,show.legend = FALSE) +
  #scale_fill_manual(values=c("#072859","#09387D","#08519C","#6BAED6")) +
  #scale_fill_manual(values=c("#01525c","#026b78","#013940","#038494")) +
  scale_fill_manual(values=c("snow3","snow2","snow4","snow1")) +
  scale_color_manual(values=c("tomato3","tomato2","tomato4","tomato1")) +
  #scale_color_grey() +
  scale_y_continuous(name = "Turnout",breaks = seq(0, 0.7, 0.1),limits=c(0,0.7)) +
  scale_x_discrete(name = "State") +
  theme_classic() #+
#geom_hline(yintercept = c(by(PostPredTurnout_Vote$Turnout,PostPredTurnout_Vote$State,median)),lty=2,col="grey50")
dev.off()













###### 8: Use Imputations Instead
Model_mat_imp <- Model_mat[,is.element(colnames(Model_mat),ImpDataNames)]
MM <- 50
Imputations <- round(seq(1,nrow(Model_mat_imp),length.out=MM))

Results <- NULL
Results$VoteBySubgroups <- round(matrix(rowMeans(apply(matrix(Imputations),1,function(x) 
  ProbVote_Imp(Model_mat_imp[x,],Data$state)$VoteBySubgroups)),byrow=T,ncol=4),2)

Results$VoteBySubgroupsSE <- round(sqrt(((1+1/MM)*matrix(apply(apply(matrix(Imputations),1,function(x) 
  ProbVote_Imp(Model_mat_imp[x,],Data$state)$VoteBySubgroups),1,var),byrow=T,ncol=4)) + 
    matrix(rowMeans(apply(matrix(Imputations),1,function(x) 
      ProbVote_Imp(Model_mat_imp[x,],Data$state)$VoteBySubgroupsVAR)),byrow=T,ncol=4)),2)

Results$SubgroupsByVote <- round(matrix(rowMeans(apply(matrix(Imputations),1,function(x) 
  ProbVote_Imp(Model_mat_imp[x,],Data$state)$SubgroupsByVote)),byrow=T,ncol=4),2)
colnames(Results$VoteBySubgroups) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroups) <- c("Full","M","F","<30","30-49","50-69","70+",
                                       "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                       "<30(F)","30-49(F)","50-69(F)","70+(F)")
colnames(Results$VoteBySubgroupsSE) <- c("FL","GA","NC","SC")
rownames(Results$VoteBySubgroupsSE) <- c("Full","M","F","<30","30-49","50-69","70+",
                                         "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                         "<30(F)","30-49(F)","50-69(F)","70+(F)")
colnames(Results$SubgroupsByVote) <- c("FL","GA","NC","SC")
rownames(Results$SubgroupsByVote) <- c("M","F","<30","30-49","50-69","70+",
                                       "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                       "<30(F)","30-49(F)","50-69(F)","70+(F)")

Results$ProbTurnout_NonRespAll <- t(apply(matrix(1:nrow(Model_mat_imp)),1,function(x) 
  ProbVoteNonrespondents_Imp(Model_mat_imp[x,],Data$state,Data$unit)$ProbTurnout_NonResp))
colnames(Results$ProbTurnout_NonRespAll) <- c("FL","GA","NC","SC")

Results$ProbTurnout_NonRespMean <- round(matrix(rowMeans(t(Results$ProbTurnout_NonRespAll)),byrow=T,ncol=4),2)
colnames(Results$ProbTurnout_NonRespMean) <- c("FL","GA","NC","SC")

#Results$ProbTurnout_NonResp <- round(matrix(rowMeans(apply(matrix(Imputations),1,function(x) 
#  ProbVoteNonrespondents_Imp(Model_mat_imp[x,],Data$state,Data$unit)$ProbTurnout_NonResp)),byrow=T,ncol=4),2)

#Results$ProbTurnout_NonRespSE <- round(sqrt(((1+1/MM)*matrix(apply(apply(matrix(Imputations),1,function(x) 
#  ProbVoteNonrespondents_Imp(Model_mat_imp[x,],Data$state,Data$unit)$ProbTurnout_NonResp),1,var),byrow=T,ncol=4)) + 
#    matrix(rowMeans(apply(matrix(Imputations),1,function(x) 
#      ProbVoteNonrespondents_Imp(Model_mat_imp[x,],Data$state,Data$unit)$ProbTurnout_NonRespVAR)),byrow=T,ncol=4)),2)

colnames(Results$ProbTurnout_NonResp) <- c("FL","GA","NC","SC")


#xtable(cbind(Vote_Margins_Mat,Results$VoteBySubgroups))
xtable(Results$VoteBySubgroups)
xtable(Results$VoteBySubgroupsSE)
xtable(Results$SubgroupsByVote)


CatalistVoterComposition <- as.data.frame(matrix(c(0.45,0.44,0.45,0.43,0.55,0.56,0.55,0.57,
                                                   0.13,0.14,0.15,0.13,0.29,0.36,0.34,0.32,
                                                   0.38,0.38,0.37,0.40,0.20,0.13,0.14,0.16,
                                                   0.06,0.06,0.07,0.05,0.13,0.15,0.15,0.14,
                                                   0.17,0.17,0.17,0.18,0.09,0.06,0.06,0.07,
                                                   0.08,0.08,0.09,0.08,0.16,0.20,0.19,0.18,
                                                   0.21,0.20,0.20,0.22,0.11,0.07,0.08,0.09),
                                                 byrow=TRUE,ncol=4))
colnames(CatalistVoterComposition) <- c("FL","GA","NC","SC")
rownames(CatalistVoterComposition) <- c("Male","Female","<30","30-49","50-69","70+",
                                        "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                        "<30(F)","30-49(F)","50-69(F)","70+(F)")

ModelVoterComposition <- Results$SubgroupsByVote
colnames(ModelVoterComposition) <- c("FL","GA","NC","SC")
rownames(ModelVoterComposition) <- c("Male","Female","<30","30-49","50-69","70+",
                                     "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                     "<30(F)","30-49(F)","50-69(F)","70+(F)")
Deviation <- ModelVoterComposition - CatalistVoterComposition


















###### 9: Calculate margins for vote by the different variables
Vote_Margins <- PostProb_Vote(PostParameters)
Vote_Margins

ImpData <- matrix(Vote_Margins$Vote_by_StateAgeGender[,1],ncol=8,byrow=T)
ImpData <-rbind(ImpData[,1:4],ImpData[,5:8])
Vote_Margins_Mat <- rbind(matrix(Vote_Margins$Vote_by_State[,1],ncol=4,byrow=T),
                          matrix(Vote_Margins$Vote_by_StateGender[,1],ncol=4,byrow=T),
                          matrix(Vote_Margins$Vote_by_StateAge[,1],ncol=4,byrow=T),ImpData)
colnames(Vote_Margins_Mat) <- c("FL","GA","NC","SC")
rownames(Vote_Margins_Mat) <- c("Full","Male","Female","<30","30-49","50-69","70+",
                                "<30(M)","30-49(M)","50-69(M)","70+(M)",
                                "<30(F)","30-49(F)","50-69(F)","70+(F)")
xtable(Vote_Margins_Mat)


###### 10: Predict New Data
NewData <- PostPred_NewData(PostParameters[,"Post mean"],Data$state)
NewR <- NewData$NewR
NewData <- NewData$NewData
#overall
table(Data$vote)/sum(table(Data$vote))
by(NewData,list(unit=NewData$unit),function(x) sum(x$vote==1)/length(x$vote))
by(NewData,list(Rvote=NewR$vote),function(x) sum(x$vote==1)/length(x$vote))
by(NewData,list(Rvote=NewR$vote,unit=NewData$unit),function(x) sum(x$vote==1)/length(x$vote))
by(NewR,list(unit=NewData$unit),function(x) sum(x$vote==1)/length(x$vote))
#by state
by(Data,list(state=Data$state),function(x) sum(x$vote==1,na.rm = T)/length(x$vote[!is.na(x$vote)]))
by(NewData,list(unit=NewData$unit,state=NewData$state),function(x) sum(x$vote==1)/length(x$vote))
by(NewData,list(Rvote=NewR$vote,state=NewData$state),function(x) sum(x$vote==1)/length(x$vote))
by(NewData,list(Rvote=NewR$vote,unit=NewData$unit,state=NewData$state),function(x) sum(x$vote==1)/length(x$vote))
by(NewR,list(unit=NewData$unit,state=NewData$state),function(x) sum(x$vote==1)/length(x$vote))

by(NewData[NewData$vote==1,],list(state=NewData$state[NewData$vote==1],vote=NewData$vote[NewData$vote==1]),
   function(x) table(x$age)/sum(table(x$age)))
by(NewData[NewData$vote==1,],list(state=NewData$state[NewData$vote==1],vote=NewData$vote[NewData$vote==1]),
   function(x) table(x$gender)/sum(table(x$gender)))
by(NewData[NewData$vote==1,],list(state=NewData$state[NewData$vote==1],vote=NewData$vote[NewData$vote==1]),
   function(x) table(x$gender,x$age)/sum(table(x$gender,x$age)))

by(NewData,list(vote=NewData$vote),function(x) sum(x$unit==0)/length(x$unit))
