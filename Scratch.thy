theory Scratch
imports Porder
begin

datatype 'a myList = 
  myNil |
  myCons 'a "'a myList"

fun myBelow :: "'a::below myList \<Rightarrow> 'a myList \<Rightarrow> bool"  where
  "myBelow myNil y = True" |
  "myBelow (myCons b xs) myNil = False" |
  "myBelow (myCons b xs) (myCons c ys) = ((below b c) \<and> (myBelow xs ys))"

instantiation myList :: (below) below
begin
  definition below_myList_def [simp]:
    "(op \<sqsubseteq>) \<equiv> (\<lambda>x y. myBelow x y)"
  instance ..
end

lemma refl_less_myList: "(x::('a::po) myList) \<sqsubseteq> x"
  apply (induction x)
  apply simp
  apply auto
  done

lemma [simp]: "y \<sqsubseteq> myNil \<Longrightarrow> myNil = y"
  apply (induction y)
  apply auto
  done

lemma antisym_help: "myBelow (myCons a x) (y::('a::po) myList) \<Longrightarrow> myBelow y (myCons a x) \<Longrightarrow> myCons a x = y"
  apply (induction y rule:myBelow.induct)
  apply auto
  apply (metis myBelow.simps(2) myList.exhaust)
  by (metis below_antisym)

lemma antisym_less_myList: "(x::('a::po) myList) \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
  apply (induction x)
  apply auto
  apply (metis myBelow.simps(2) myList.exhaust)
  by (metis antisym_help)

lemma trans_help: "(\<And>y. myBelow ys y \<Longrightarrow> myBelow y xs \<Longrightarrow> myBelow ys xs) \<Longrightarrow>
       myBelow (myCons c ys) (z::('a::po) myList)  \<Longrightarrow> myBelow z (myCons b xs) \<Longrightarrow> myBelow ys xs"
  by (metis myBelow.elims(2) myBelow.simps(3) myList.distinct(1) myList.exhaust)

lemma trans_less_myList: "(x::('a::po) myList) \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
  apply (induction x arbitrary: y rule:myBelow.induct)
  apply auto
  apply (metis myBelow.elims(2) myBelow.simps(3) myList.distinct(1) myList.exhaust rev_below_trans)
  by (metis trans_help)
  
instantiation myList :: (po)po 
begin
  instance 
  apply intro_classes
  apply (metis refl_less_myList)
  apply (metis trans_less_myList)
  apply (metis antisym_less_myList)
  done
end
