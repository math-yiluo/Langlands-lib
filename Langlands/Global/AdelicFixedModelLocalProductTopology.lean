import Langlands.Global.AdelicFixedModelSystem
import Langlands.Global.AdelicLocalFactorUnitsProof
import Langlands.AlgebraicGeometry.PointTopology.LocalProductPointBaseChange

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- Coefficient transport and genuine base change give the same induced
product topology on points of the original model. -/
theorem induced_baseChange_productPointTopology
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {ι : Type u} (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Algebra A (R i)] [∀ i, Algebra B (R i)] [∀ i, IsScalarTower A B (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, IsTopologicalRing (R i)]
    [∀ i, IsLocalRing (R i)] [∀ i, IsOpenUnits (R i)]
    (X : Over (Spec (CommRingCat.of A))) (e : C ≃ₐ[B] ∀ i, R i) :
    TopologicalSpace.induced (ringPointBaseChangeEquiv A B C X)
        (TopologicalSpace.induced (ringPointChangeRingEquiv B (ringBaseChange A B X) e)
          (localProductPointTopology B R (ringBaseChange A B X))) =
      TopologicalSpace.induced (ringPointChangeRingEquiv A X (e.restrictScalars A))
        (localProductPointTopology A R X) := by
  let := localProductPointTopology A R X
  let := localProductPointTopology B R (ringBaseChange A B X)
  let H := localProductPointBaseChangeHomeomorph A B R X
  have hmap : ringPointChangeRingEquiv B (ringBaseChange A B X) e ∘
        ringPointBaseChangeEquiv A B C X =
      H ∘ ringPointChangeRingEquiv A X (e.restrictScalars A) := by
    funext p
    exact (ringPointBaseChangeEquiv_changeRing A B C (∀ i, R i) X e.toAlgHom p).symm
  rw [induced_compose, hmap, ← induced_compose, ← H.isInducing.eq_induced]

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global.FixedModelLocalProduct

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  (S : Finset (AlgebraicCurve.Place k F)) (T : AdelicLevelIndexAbove S)

/-- Literal inclusion of the fixed integral base into the enlarged one. -/
scoped instance curveBaseAlgebra :
    Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
  (curvePlaceSIntegersMap k F T.property).toAlgebra

/-- Retain the original enlarged integral-base action on its literal level ring. -/
scoped instance curveLevelAlgebra :
    Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
  inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))

/-- Restrict the original local scalar action along the original integer inclusion. -/
scoped instance (priority := 100) curveFactorAlgebra (i : CurvePlaceLevelFactorIndex k F T.val) :
    Algebra (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F T.val i) :=
  ((algebraMap (curvePlaceSIntegers k F T.val) (CurvePlaceLevelFactor k F T.val i)).comp
    (curvePlaceSIntegersMap k F T.property)).toAlgebra

scoped instance curveFactorTower (i : CurvePlaceLevelFactorIndex k F T.val) :
    IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (CurvePlaceLevelFactor k F T.val i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance curveLevelTower :
    IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance curveOpenUnits (i : CurvePlaceLevelFactorIndex k F T.val) :
    IsOpenUnits (CurvePlaceLevelFactor k F T.val i) := by
  exact adelicLocalFactorUnits.1 k F T.val i

/-- The original enlarged level product, respecting the fixed integral base. -/
def curveFactorAlgEquiv :
    curvePlaceAdeleLevelOver k F S T ≃ₐ[curvePlaceSIntegers k F S]
      ∀ i, CurvePlaceLevelFactor k F T.val i :=
  { curvePlaceLevelFactorRingEquiv k F T.val with commutes' := fun _ => rfl }

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- The existing fixed-model stage topology is the local product topology over
the original integral base, after the literal level coefficient comparison. -/
theorem curveStageTopology_eq :
    curvePlaceFixedModelStageTopology k F S X T =
      TopologicalSpace.induced
        (ringPointChangeRingEquiv (curvePlaceSIntegers k F S) X (curveFactorAlgEquiv k F S T))
        (localProductPointTopology (curvePlaceSIntegers k F S)
          (CurvePlaceLevelFactor k F T.val) X) := by
  unfold curvePlaceFixedModelStageTopology
  rw [curvePlaceLevelModelPointTopology_eq]
  exact induced_baseChange_productPointTopology
    (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
    (curvePlaceAdeleLevelOver k F S T) (CurvePlaceLevelFactor k F T.val) X
    (curvePlaceLevelFactorAlgEquiv k F T.val)

/-- Actual fixed-base arithmetic stage points and original fixed-base product
points are homeomorphic for their independently defined topologies. -/
def curveStageHomeomorph :
    @Homeomorph
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (RingPoint (curvePlaceSIntegers k F S) X (∀ i, CurvePlaceLevelFactor k F T.val i))
      (curvePlaceFixedModelStageTopology k F S X T)
      (localProductPointTopology (curvePlaceSIntegers k F S)
        (CurvePlaceLevelFactor k F T.val) X) := by
  letI := curvePlaceFixedModelStageTopology k F S X T
  letI := localProductPointTopology (curvePlaceSIntegers k F S)
    (CurvePlaceLevelFactor k F T.val) X
  exact (ringPointChangeRingEquiv (curvePlaceSIntegers k F S) X
    (curveFactorAlgEquiv k F S T)).toHomeomorphOfIsInducing
      ⟨curveStageTopology_eq k F S T X⟩

/-- The comparison retains precisely the original coefficient-point map. -/
@[simp]
theorem curveStageHomeomorph_apply
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curveStageHomeomorph k F S T X p = p.changeRing (curveFactorAlgEquiv k F S T).toAlgHom := rfl

/-- Every coordinate is the original literal projection from the enlarged level. -/
theorem curveStageHomeomorph_coordinate
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
    (i : CurvePlaceLevelFactorIndex k F T.val) :
    (productPointMap (curvePlaceSIntegers k F S) (CurvePlaceLevelFactor k F T.val) X
      (curveStageHomeomorph k F S T X p) i).left =
        Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorProjection k F T.val i)) ≫ p.left := by
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) ≫
      (Spec.map (CommRingCat.ofHom (curvePlaceLevelFactorRingEquiv k F T.val).toRingHom) ≫
        p.left) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The fixed-base comparison is natural in the original integral model. -/
theorem curveStageHomeomorph_natural
    {Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))} (f : X ⟶ Y)
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curveStageHomeomorph k F S T Y (p ≫ f) = curveStageHomeomorph k F S T X p ≫ f := by
  change ringTestMap _ _ ≫ (p ≫ f) = (ringTestMap _ _ ≫ p) ≫ f
  exact (Category.assoc _ _ _).symm

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- Literal inclusion of the fixed integral base into the enlarged one. -/
scoped instance numberFieldBaseAlgebra :
    Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
  (numberFieldSIntegersMap K T.property).toAlgebra

/-- Retain the original enlarged integral-base action on its literal full level ring. -/
scoped instance numberFieldLevelAlgebra :
    Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
  inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))

/-- Restrict each original local scalar action along the original integer inclusion. -/
scoped instance (priority := 100) numberFieldFactorAlgebra (i : NumberFieldLevelFactorIndex K T.val) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T.val i) :=
  ((algebraMap ((T.val : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T.val i)).comp
    (numberFieldSIntegersMap K T.property)).toAlgebra

scoped instance numberFieldFactorTower (i : NumberFieldLevelFactorIndex K T.val) :
    IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (NumberFieldLevelFactor K T.val i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance numberFieldLevelTower :
    IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance numberFieldOpenUnits (i : NumberFieldLevelFactorIndex K T.val) :
    IsOpenUnits (NumberFieldLevelFactor K T.val i) := by
  exact adelicLocalFactorUnits.2 K T.val i

/-- The original full enlarged level product, respecting the fixed integral base. -/
def numberFieldFactorAlgEquiv :
    numberFieldAdeleLevelOver K S T ≃ₐ[((S : Set (FinitePlace K)).integer K)]
      ∀ i, NumberFieldLevelFactor K T.val i :=
  { numberFieldLevelFactorRingEquiv K T.val with commutes' := fun _ => rfl }

variable (X : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- The existing full fixed-model stage topology is the original fixed-base
local product topology after the literal full-level coefficient comparison. -/
theorem numberFieldStageTopology_eq :
    numberFieldFixedModelStageTopology K S X T =
      TopologicalSpace.induced
        (ringPointChangeRingEquiv ((S : Set (FinitePlace K)).integer K) X
          (numberFieldFactorAlgEquiv K S T))
        (localProductPointTopology ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K T.val) X) := by
  unfold numberFieldFixedModelStageTopology
  rw [numberFieldLevelModelPointTopology_eq]
  exact induced_baseChange_productPointTopology
    ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOver K S T) (NumberFieldLevelFactor K T.val) X
    (numberFieldLevelFactorAlgEquiv K T.val)

/-- Full fixed-base arithmetic stage points and original fixed-base product
points have the same independently defined topology. -/
def numberFieldStageHomeomorph :
    @Homeomorph
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (∀ i, NumberFieldLevelFactor K T.val i))
      (numberFieldFixedModelStageTopology K S X T)
      (localProductPointTopology ((S : Set (FinitePlace K)).integer K)
        (NumberFieldLevelFactor K T.val) X) := by
  letI := numberFieldFixedModelStageTopology K S X T
  letI := localProductPointTopology ((S : Set (FinitePlace K)).integer K)
    (NumberFieldLevelFactor K T.val) X
  exact (ringPointChangeRingEquiv ((S : Set (FinitePlace K)).integer K) X
    (numberFieldFactorAlgEquiv K S T)).toHomeomorphOfIsInducing
      ⟨numberFieldStageTopology_eq K S T X⟩

/-- The full comparison retains precisely the original coefficient-point map. -/
@[simp]
theorem numberFieldStageHomeomorph_apply
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldStageHomeomorph K S T X p =
      p.changeRing (numberFieldFactorAlgEquiv K S T).toAlgHom := rfl

/-- Every full coordinate, including every infinite place, is the original projection. -/
theorem numberFieldStageHomeomorph_coordinate
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) :
    (productPointMap ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T.val) X
      (numberFieldStageHomeomorph K S T X p) i).left =
        Spec.map (CommRingCat.ofHom (numberFieldLevelFactorProjection K T.val i)) ≫ p.left := by
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i)) ≫
      (Spec.map (CommRingCat.ofHom (numberFieldLevelFactorRingEquiv K T.val).toRingHom) ≫
        p.left) = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The full fixed-base comparison is natural in the original integral model. -/
theorem numberFieldStageHomeomorph_natural
    {Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))} (f : X ⟶ Y)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldStageHomeomorph K S T Y (p ≫ f) =
      numberFieldStageHomeomorph K S T X p ≫ f := by
  change ringTestMap _ _ ≫ (p ≫ f) = (ringTestMap _ _ ≫ p) ≫ f
  exact (Category.assoc _ _ _).symm

end NumberField

end Langlands.Global.FixedModelLocalProduct
