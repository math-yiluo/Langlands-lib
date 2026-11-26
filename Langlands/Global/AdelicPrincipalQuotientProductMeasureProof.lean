import Langlands.Global.AdelicPrincipalQuotientProductMeasureStatement
import Langlands.Global.LeftCosetProductMeasureStatement

/-! # Specialization of the discrete quotient product law to the full adelic quotient -/

noncomputable section

set_option autoImplicit false

open MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.RestrictionSplitCentre

open AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false in
/-- The count-normalized quotient product law with the canonical adelic factors, from the
product formula for discrete left quotients. -/
theorem principalQuotientProductMeasure_of_productQuotientMeasure
    (hPQ : LeftCosetSpace.ProductQuotientMeasureStatement.{0, 0, 0}) :
    PrincipalQuotientProductMeasureStatement := by
  intro F _ _ G _ _ hG
  have hquot := hPQ
    (A := PositiveRealTorus.intrinsicSubgroup F (canonicalTorus F G))
    (N := normOneSubgroup F G) (G := AdelicGroupPoints F G)
    (intrinsicNormOneDecomposition F G hG) (rationalNormOneSubgroup F G)
    (AdelicGroupPoints.rationalSubgroup F G)
    (intrinsicNormOneDecomposition_mem_principal F G hG)
    (isDiscrete_rationalNormOneSubgroup F G) (isDiscrete_rationalSubgroup F G)
    (intrinsicCentreHaarMeasure F G hG) Measure.haar Measure.haar
    (measurePreserving_intrinsicNormOneDecomposition F G hG)
  have hprod := (measurePreserving_positiveCentreEquiv F G hG).prod
    (measurePreserving_canonicalNormOneQuotientHomeomorph F G hG)
  exact hprod.comp hquot

end Langlands.Global.RestrictionSplitCentre
