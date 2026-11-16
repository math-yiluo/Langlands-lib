import Langlands.Global.RankinSelberg.EqualUnfoldingReduction

/-! # The gauge integrability premises of the equal-rank unfolding, for all pairs -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Premises G and G̃ of `EqualUnfoldingReductionStatement` for every equal-rank pair of
cuspidal realizations (Cogdell 2004, pp.210–211: the unfolded integral converges for
`Re s ≫ 0`, and its dual analogue for `Re s ≪ 0`). -/
def EqualUnfoldingGaugeStatement : Prop :=
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r),
    EqualWhittakerGaugeIntegrable F T T') ∧
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r),
    DualEqualWhittakerGaugeIntegrable F T T')

end Langlands.Global.RankinSelbergGlobal
