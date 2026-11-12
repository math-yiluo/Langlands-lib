import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing

/-! # The completion of a regular local ring is regular -/

namespace Langlands.CommutativeAlgebra.FiniteTypeIntGRing

open IsLocalRing

/-- The maximal-ideal adic completion of a regular local ring is a regular local ring. -/
theorem isRegularLocalRing_adicCompletion (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  have : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing _
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, IsRegularLocalRing.spanFinrank_maximalIdeal,
    ← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))]
  exact_mod_cast le_self_add

end Langlands.CommutativeAlgebra.FiniteTypeIntGRing
