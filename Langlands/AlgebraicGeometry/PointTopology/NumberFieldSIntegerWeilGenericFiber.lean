import Langlands.Global.NumberFieldSIntegerFinite
import Langlands.AlgebraicGeometry.PointTopology.IntegralClosureWeilRestrictionGenericFiber

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry Langlands.Global
open scoped NumberField Langlands.Global Langlands.Global.NumberFieldSIntegers

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K))

variable (Y : Over (Spec (CommRingCat.of (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)))) [LocallyOfFiniteType Y.hom]

local instance sIntegerGenericFiberLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd Y.hom (Spec.algebraMap (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L)))

/-- The actual S-integer Weil model has the original field Weil scheme as generic fiber. -/
def numberFieldSIntegersWeilGenericFiberIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom) :
    ringBaseChange ((S : Set (FinitePlace K)).integer K) K (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y) ≅
      affineChartWeilRestriction K L (ringBaseChange (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L Y) :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) K L Y n j hj

/-- Every original test point preserves the same integral counit under the generic-fiber iso. -/
theorem numberFieldSIntegersWeilGenericFiberIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) n = Y.hom)
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange ((S : Set (FinitePlace K)).integer K) K (affineChartWeilRestriction ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) Y)) :
    affineChartWeilRestrictionComparison K L (ringBaseChange (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) L Y) T
        (p ≫ (numberFieldSIntegersWeilGenericFiberIso K L S Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) K L
        (integralClosureFractionTensorEquiv ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) K L)
        (integralClosureFractionTensorEquiv_one_tmul ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) K L) Y T p :=
  projectiveImmersionIntegralClosureWeilRestrictionGenericFiberIso_comparison
    ((S : Set (FinitePlace K)).integer K) (((numberFieldExceptionalPreimage (L := L) S : Finset (FinitePlace L)) : Set (FinitePlace L)).integer L) K L Y n j hj T p

end Langlands.AlgebraicGeometry.PointTopology
