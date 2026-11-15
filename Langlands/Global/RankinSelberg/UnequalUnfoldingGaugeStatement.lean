import Langlands.Global.RankinSelberg.UnequalUnfoldingReduction

/-! # The gauge integrability premises of the unequal-rank unfolding, for all pairs -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Premises G and G' of `UnequalUnfoldingReductionStatement` for every actual positive
unequal-rank cuspidal pair (Cogdell 2004, pp.206–207: absolute convergence for `Re s ≫ 0` by
the gauge estimates). -/
def UnequalUnfoldingGaugeStatement : Prop :=
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    WhittakerGaugeIntegrable F h T T') ∧
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    DualWhittakerGaugeIntegrable F h T T')

end Langlands.Global.RankinSelbergGlobal
