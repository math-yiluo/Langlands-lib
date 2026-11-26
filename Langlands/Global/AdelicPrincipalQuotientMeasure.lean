import Langlands.Global.AdelicPrincipalQuotientProductMeasureProof
import Langlands.Global.LeftCosetProductMeasureProof

/-! # The canonical Haar product on the full principal adelic quotient -/

set_option autoImplicit false

namespace Langlands.Global.RestrictionSplitCentre

/-- The canonical measurable equivalence `G(F) \ G(𝔸) ≃ A_G × [G]` carries the fixed
count-normalized rational quotient measure to the product of the positive-centre Haar measure
and the canonical measure on `[G]`. -/
theorem principalQuotientProductMeasure : PrincipalQuotientProductMeasureStatement :=
  principalQuotientProductMeasure_of_productQuotientMeasure LeftCosetSpace.productQuotientMeasure

end Langlands.Global.RestrictionSplitCentre
