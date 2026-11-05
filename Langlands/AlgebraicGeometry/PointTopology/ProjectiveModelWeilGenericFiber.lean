import Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionModelGenericFiber
import Langlands.AlgebraicGeometry.PointTopology.IntegralClosureWeilRestrictionGenericFiber
import Langlands.Global.NumberFieldSIntegerFinite
import Langlands.Global.CurvePlacePrincipalProjectiveModel

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry Langlands.Global
open scoped Langlands.AlgebraicGeometry.NoetherianApproximation.ProjectiveImmersionRingModelData
  NumberField Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegers
  AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin

namespace Langlands.AlgebraicGeometry.PointTopology

open NoetherianApproximation

set_option backward.isDefEq.respectTransparency false

local instance originalProjectiveSchemeLocallyOfFiniteType
    (L : Type u) [Field L] {X : Scheme.{u}} {n : ℕ}
    {j : X ⟶ ProjectiveSpace L n} [IsImmersion j] :
    LocallyOfFiniteType (Over.mk (j ≫ projectiveSpaceToSpec L n)).hom := by
  change LocallyOfFiniteType (j ≫ projectiveSpaceToSpec L n)
  infer_instance

local instance originalProjectiveSchemeSeparated
    (L : Type u) [Field L] {X : Scheme.{u}} {n : ℕ}
    {j : X ⟶ ProjectiveSpace L n} [IsImmersion j] :
    IsSeparated (Over.mk (j ≫ projectiveSpaceToSpec L n)).hom :=
  isSeparated_of_projectiveImmersion L _ n j rfl

section General

variable (A B K L : Type u)
  [CommRing A] [IsDomain A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]
  [Algebra A B] [Algebra B L] [IsScalarTower A B L] [IsIntegralClosure B A L]
  [Module.Finite A B] [Module.Projective A B]
  {X : Scheme.{u}} {n : ℕ} {j : X ⟶ ProjectiveSpace L n} [IsImmersion j]
  (D : ProjectiveImmersionRingModelData B L X n j)

local instance modelOriginalGenericFiberLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange B L D.asOver).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (CategoryTheory.Limits.pullback.snd D.asOver.hom (Spec.algebraMap B L)))

local instance modelOriginalGenericFiberSeparated :
    IsSeparated (ringBaseChange B L D.asOver).hom :=
  inferInstanceAs (IsSeparated
    (CategoryTheory.Limits.pullback.snd D.asOver.hom (Spec.algebraMap B L)))

/-- The actual integral Weil model has the Weil restriction of the original field scheme as generic fiber. -/
def projectiveModelWeilGenericFiberIso :
    ringBaseChange A K (affineChartWeilRestriction A B D.asOver) ≅
      affineChartWeilRestriction K L (Over.mk (j ≫ projectiveSpaceToSpec L n)) :=
  (integralClosureWeilRestrictionGenericFiberIso A B K L D.asOver
      D.hasFiniteAffineNeighborhoods) ≪≫
    affineChartWeilRestrictionTargetIso K L
      (hasFiniteAffineNeighborhoods_ringBaseChange B L D.asOver D.hasFiniteAffineNeighborhoods)
      (hasFiniteAffineNeighborhoods_of_projectiveImmersion L n j) D.genericFiberIso

/-- On every original test, the generic-fiber iso preserves the integral counit followed by the original-model iso. -/
theorem projectiveModelWeilGenericFiberIso_comparison
    (T : Over (Spec (CommRingCat.of K)))
    (p : T ⟶ ringBaseChange A K (affineChartWeilRestriction A B D.asOver)) :
    affineChartWeilRestrictionComparison K L (Over.mk (j ≫ projectiveSpaceToSpec L n)) T
        (p ≫ (projectiveModelWeilGenericFiberIso A B K L D).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison A B K L
        (integralClosureFractionTensorEquiv A B K L)
        (integralClosureFractionTensorEquiv_one_tmul A B K L) D.asOver T p ≫
          D.genericFiberIso.hom := by
  dsimp only [projectiveModelWeilGenericFiberIso, Iso.trans_hom]
  rw [← Category.assoc, affineChartWeilRestrictionTargetIso_comparison,
    integralClosureWeilRestrictionGenericFiberIso_comparison]

end General

section NumberField

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : Finset (FinitePlace L))
  (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

/-- The constructed original number-field model yields the Weil scheme of the originally specified X. -/
def numberFieldProjectiveModelWeilGenericFiberIso
    (M : NumberFieldExtensionProjectiveModelData K L S T X n j) :
    let A := (M.exceptional : Set (FinitePlace K)).integer K
    let B := (((numberFieldExceptionalPreimage (L := L) M.exceptional :
      Finset (FinitePlace L)) : Set (FinitePlace L)).integer L)
    ringBaseChange A K (affineChartWeilRestriction A B M.geometric.asOver) ≅
      affineChartWeilRestriction K L (Over.mk (j ≫ projectiveSpaceToSpec L n)) :=
  projectiveModelWeilGenericFiberIso
    ((M.exceptional : Set (FinitePlace K)).integer K) _ K L M.geometric

end NumberField

section Curve

open IntermediateField

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (S : Finset (AlgebraicCurve.Place k K)) (T : Finset (AlgebraicCurve.Place k L))
  (X : Scheme.{u}) (n : ℕ) (j : X ⟶ ProjectiveSpace L n) [IsImmersion j]

/-- The constructed principal curve model yields the Weil scheme of the originally specified X. -/
def curvePlacePrincipalProjectiveModelWeilGenericFiberIso
    (M : CurvePlacePrincipalProjectiveModelData k K L s S T X n j) :
    letI : Fact (M.denominator ≠ 0) := ⟨M.denominator_ne_zero⟩
    let A := curvePlaceSIntegers k K
      (curvePlacePrincipalExceptional k K s (M.denominator : K))
    let B := curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L)
      (curvePlacePrincipalExceptional k K s (M.denominator : K)))
    ringBaseChange A K (affineChartWeilRestriction A B M.geometric.asOver) ≅
      affineChartWeilRestriction K L (Over.mk (j ≫ projectiveSpaceToSpec L n)) := by
  letI : Fact (M.denominator ≠ 0) := ⟨M.denominator_ne_zero⟩
  exact projectiveModelWeilGenericFiberIso
    (curvePlaceSIntegers k K (curvePlacePrincipalExceptional k K s (M.denominator : K)))
    _ K L M.geometric

end Curve

end Langlands.AlgebraicGeometry.PointTopology
