import Langlands.Global.CurvePlacePrincipalSIntegerFinite
import Langlands.AlgebraicGeometry.PointTopology.IntegralClosureWeilRestrictionGenericFiber

noncomputable section

universe u

open CategoryTheory IntermediateField
open _root_.AlgebraicGeometry Langlands.Global
open scoped AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : AlgebraicCurve.CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))))) [LocallyOfFiniteType Y.hom]

local instance principalSIntegerGenericFiberLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) L Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd Y.hom (Spec.algebraMap (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) L)))

/-- The actual curve S-integer Weil model has the original field Weil scheme as generic fiber. -/
def curvePlacePrincipalSIntegersWeilGenericFiberIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom) :
    ringBaseChange (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y) ≅
      affineChartWeilRestriction K L (ringBaseChange (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) L Y) :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) K L Y n j hj

/-- The generic-fiber isomorphism retains the original integral counit on all original tests. -/
theorem curvePlacePrincipalSIntegersWeilGenericFiberIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) n = Y.hom)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) K (affineChartWeilRestriction (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) L Y) T
        (p ≫ (curvePlacePrincipalSIntegersWeilGenericFiberIso k K L s t Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) K L
        (integralClosureFractionTensorEquiv (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) K L)
        (integralClosureFractionTensorEquiv_one_tmul (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) K L) Y T p :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso_comparison
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (t : K))) (curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) K L Y n j hj T p

end Langlands.AlgebraicGeometry.PointTopology
