import Langlands.Global.RankinSelberg.DualExpansionFinal

/-! # The expansion of the dual projection from `J` and the dual Whittaker expansion -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

/-- Premise E' of `UnequalUnfoldingReductionStatement` follows from the rectangular modulus
statement `J` and the dual Whittaker expansion: if right multiplication by `g ∈ GL_m(𝔸)` scales
the rectangular Haar measure by `|det g|^{-k}`, then for every actual positive unequal-rank pair of
ranks, if the dual cusp forms of `T` have their Whittaker expansions over `N_r(F) \ GL_r(F)` with
locally uniform absolute convergence, the dual projection `P̃^n_m φ̃` has its expansion over
`N_m(F) \ GL_m(F)` in terms of the rectangle integrals of the dual Whittaker function
(Cogdell 2004, §2.2, p.207). -/
def DualProjectionExpansionReductionStatement : Prop :=
  RectangleMeasureModulusStatement.{u} →
    ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
      (r t : ℕ) (h : t < r) (T : Automorphic.CuspidalOperatorRealization F r),
      DualCuspidalWhittakerExpansion F T → DualProjectionWhittakerExpansion F h T

/-- Proof of `DualProjectionExpansionReductionStatement`. -/
theorem dualProjectionExpansionReduction : DualProjectionExpansionReductionStatement.{u} :=
  fun hJ _ _ _ _ _ _ h T hT =>
    dualProjectionWhittakerExpansion_of_dualCuspidalWhittakerExpansion hJ h T hT

end Langlands.Global.RankinSelbergGlobal
