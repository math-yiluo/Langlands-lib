import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement

/-! # Reduction of the original Harris singleton branch to the totally complex branch -/

universe uF uV

namespace Langlands.Global.Harris

/-- Specializing the foundational transfer and rigidity premises to totally
complex fields reduces the original singleton branch to its TC companion. -/
def Proposition48SingletonBranchReductionStatement : Prop :=
  Proposition48SingletonBranchTCStatement.{uF, uV} →
  Proposition48SingletonBranchStatement.{uF, uV}

end Langlands.Global.Harris
