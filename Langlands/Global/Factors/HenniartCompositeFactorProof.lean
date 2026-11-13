import Langlands.Global.Factors.HenniartCompositeMapStatement
import Langlands.Global.Factors.HenniartCompositeFactorDeterminant
import Langlands.Global.Factors.HenniartCompositeFactorPair

/-!
# Proof of the transport of the factor clauses to Henniart's composite map

`HenniartCompositeFactorStatement`: if an isometry `T` between the relative Weil
and automorphic images at a finite place `v` has the determinant clause at `F_v`
for every geometric reciprocity candidate, and the pair L- and epsilon-factor
clauses at `F_v` for every additive character, then for every `ℚ_p`-algebra
isomorphism `f : K ≅ F_v` the composite `henniartCompositeMap` at `K` has the
determinant clause for every geometric reciprocity candidate of `K` and the
pair-factor clause for every additive character of `K`.
-/

noncomputable section

universe uF uK uW uP uE

namespace Langlands.Global.PoleComparison

/-- **Transport of the determinant and pair-factor clauses.** The determinant
clause at `K` comes from `determinantCompatibility_henniartCompositeMap` and the
pair-factor clause at `K` from `pairFactorCompatibility_henniartCompositeMap`. -/
theorem henniartCompositeFactor :
    HenniartCompositeFactorStatement.{uF, uK, uW, uP, uE} := by
  intro F E _ _ _ _ _ _ _ c v T hT p _ h K f
  exact ⟨fun e he => determinantCompatibility_henniartCompositeMap F E c v h K f T hT.1 e he,
    fun ψ => pairFactorCompatibility_henniartCompositeMap F E c v h K f T hT.2 ψ⟩

end Langlands.Global.PoleComparison
