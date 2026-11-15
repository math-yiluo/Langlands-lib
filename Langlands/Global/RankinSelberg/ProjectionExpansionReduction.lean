import Langlands.Global.RankinSelberg.ProjectionExpansion

/-! # The expansion of the projection from the Whittaker expansion of cusp forms -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

/-- Every vector of every actual positive-rank cuspidal realization has its Whittaker
expansion, for every standard additive character (Cogdell 2004, Theorem 1.1; Shalika 1974,
Theorem 5.9). -/
def CuspidalWhittakerExpansionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r), CuspidalWhittakerExpansion F T

/-- Premise E of `UnequalUnfoldingReductionStatement` follows from the Whittaker expansion of
the cusp forms: for every actual positive unequal-rank pair of ranks, if the vectors of `T` have
their Whittaker expansions over `N_r(F) \ GL_r(F)`, then the projection `P^n_m φ` has its
expansion over `N_m(F) \ GL_m(F)` (Cogdell 2004, p.205). -/
def ProjectionExpansionReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r) (T : Automorphic.CuspidalOperatorRealization F r),
    CuspidalWhittakerExpansion F T → ProjectionWhittakerExpansion F h T

/-- Proof of `ProjectionExpansionReductionStatement`. -/
theorem projectionExpansionReduction : ProjectionExpansionReductionStatement.{u} :=
  fun F _ _ _ _ _ h T hT => projectionWhittakerExpansion_of_cuspidalWhittakerExpansion F h T hT

end Langlands.Global.RankinSelbergGlobal
