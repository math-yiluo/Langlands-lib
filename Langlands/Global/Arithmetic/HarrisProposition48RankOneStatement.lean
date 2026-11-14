import Langlands.Global.Arithmetic.HarrisProposition48InductionData

/-! # The rank-one starting case of Harris's Proposition 4.8 -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

/-- Harris 1998, proof of Proposition 4.8, p.202: the degree-one case
is supplied by the Hecke character itself, realized on `GL(1)`. -/
def Proposition48RankOneStatement : Prop :=
  ∀ Q : Proposition48Problem.{uF}, Q.IsValid →
    Module.finrank Q.E Q.E' = 1 → Q.HasSolution.{uF, uV}

end Langlands.Global.Harris
