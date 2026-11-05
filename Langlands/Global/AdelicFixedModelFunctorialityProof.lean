import Langlands.Global.AdelicFixedModelFunctorialityStatement
import Langlands.Global.AdelicLevelModelFunctorialityProof

/-! # Continuity of actual full-adele model postcomposition -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- The fixed-model comparison is natural for actual model morphisms. -/
theorem curvePlaceFixedModelPointEquiv_natural (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S)
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curvePlaceFixedModelPointEquiv k F S Y T (p ≫ f) =
      curvePlaceFixedModelPointEquiv k F S X T p ≫
        (Over.pullback
          (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))).map f := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv_natural (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) f p

/-- Postcomposition is continuous on every original fixed-base arithmetic stage. -/
theorem curvePlaceFixedModelStage_continuous (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S) :
    Continuous[curvePlaceFixedModelStageTopology k F S X T,
      curvePlaceFixedModelStageTopology k F S Y T]
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))) := by
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceFixedModelStageTopology k F S Y T
  let := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  let := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property Y)
  let eX := curvePlaceFixedModelPointHomeomorph k F S X T
  let eY := curvePlaceFixedModelPointHomeomorph k F S Y T
  let fT : curvePlaceLevelModelBaseChange k F T.property X ⟶
      curvePlaceLevelModelBaseChange k F T.property Y :=
    (Over.pullback
      (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))).map f
  have hf := adelicLevelModelFunctoriality.1 k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
    (curvePlaceLevelModelBaseChange k F T.property Y) fT
  refine (eY.symm.continuous.comp (hf.comp eX.continuous)).congr ?_
  intro p
  change (curvePlaceFixedModelPointEquiv k F S Y T).symm
    (curvePlaceFixedModelPointEquiv k F S X T p ≫ _) = p ≫ f
  exact (congrArg (curvePlaceFixedModelPointEquiv k F S Y T).symm
    (curvePlaceFixedModelPointEquiv_natural k F S f T p)).symm.trans
      ((curvePlaceFixedModelPointEquiv k F S Y T).symm_apply_apply (p ≫ f))

/-- Actual model postcomposition is continuous for the full-adele final topology. -/
theorem curvePlaceFixedModelAdele_continuous (f : X ⟶ Y) :
    Continuous[curvePlaceFixedModelAdelePointTopology k F S X,
      curvePlaceFixedModelAdelePointTopology k F S Y]
      (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
        (p ≫ f : CurvePlaceFixedModelAdelePoints k F S Y)) := by
  let R : Type u := curvePlaceSIntegers k F S
  let D := curvePlaceAdeleLevelOverDiagram k F S
  let c := curvePlaceAdeleOverCocone k F S
  let τX := curvePlaceFixedModelStageTopology k F S X
  let τY := curvePlaceFixedModelStageTopology k F S Y
  let : TopologicalSpace (RingPoint R X c.pt) := curvePlaceFixedModelAdelePointTopology k F S X
  let : TopologicalSpace (RingPoint R Y c.pt) := curvePlaceFixedModelAdelePointTopology k F S Y
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Y
  apply (ringPointCoconeTopology_continuous_iff R D X τX c (Y := RingPoint R Y c.pt)
    (fun p : RingPoint R X c.pt => (p ≫ f : RingPoint R Y c.pt))).2
  intro T
  let : TopologicalSpace (RingPoint R X (D.obj T)) := τX T
  let : TopologicalSpace (RingPoint R Y (D.obj T)) := τY T
  have hi := ringPointCoconeTopology_continuous_ι R D Y τY c T
  have hf := curvePlaceFixedModelStage_continuous k F S f T
  refine (hi.comp hf).congr ?_
  intro p
  exact (Category.assoc _ _ _).symm

/-- Actual model isomorphisms induce homeomorphisms for the original final topologies. -/
def curvePlaceFixedModelIsoHomeomorph (e : X ≅ Y) :
    @Homeomorph (CurvePlaceFixedModelAdelePoints k F S X)
      (CurvePlaceFixedModelAdelePoints k F S Y)
      (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S Y) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Y
  exact {
  toEquiv :=
    { toFun := fun p => p ≫ e.hom
      invFun := fun p => p ≫ e.inv
      left_inv := by
        intro p
        exact (Category.assoc p e.hom e.inv).trans
          ((congrArg (fun a => p ≫ a) e.hom_inv_id).trans (Category.comp_id p))
      right_inv := by
        intro p
        exact (Category.assoc p e.inv e.hom).trans
          ((congrArg (fun a => p ≫ a) e.inv_hom_id).trans (Category.comp_id p)) }
  continuous_toFun := curvePlaceFixedModelAdele_continuous k F S e.hom
  continuous_invFun := curvePlaceFixedModelAdele_continuous k F S e.inv }

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))
variable {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- The fixed-model comparison is natural for actual model morphisms. -/
theorem numberFieldFixedModelPointEquiv_natural (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S)
    (p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldFixedModelPointEquiv K S Y T (p ≫ f) =
      numberFieldFixedModelPointEquiv K S X T p ≫
        (Over.pullback
          (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map f := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv_natural ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) f p

/-- Postcomposition is continuous on every original fixed-base arithmetic stage. -/
theorem numberFieldFixedModelStage_continuous (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S) :
    Continuous[numberFieldFixedModelStageTopology K S X T,
      numberFieldFixedModelStageTopology K S Y T]
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevelOver K S T))) := by
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldFixedModelStageTopology K S Y T
  let := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  let := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property Y)
  let eX := numberFieldFixedModelPointHomeomorph K S X T
  let eY := numberFieldFixedModelPointHomeomorph K S Y T
  let fT : numberFieldLevelModelBaseChange K T.property X ⟶
      numberFieldLevelModelBaseChange K T.property Y :=
    (Over.pullback
      (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map f
  have hf := adelicLevelModelFunctoriality.2 K T.val
    (numberFieldLevelModelBaseChange K T.property X)
    (numberFieldLevelModelBaseChange K T.property Y) fT
  refine (eY.symm.continuous.comp (hf.comp eX.continuous)).congr ?_
  intro p
  change (numberFieldFixedModelPointEquiv K S Y T).symm
    (numberFieldFixedModelPointEquiv K S X T p ≫ _) = p ≫ f
  exact (congrArg (numberFieldFixedModelPointEquiv K S Y T).symm
    (numberFieldFixedModelPointEquiv_natural K S f T p)).symm.trans
      ((numberFieldFixedModelPointEquiv K S Y T).symm_apply_apply (p ≫ f))

/-- Actual model postcomposition is continuous for the full-adele final topology. -/
theorem numberFieldFixedModelAdele_continuous (f : X ⟶ Y) :
    Continuous[numberFieldFixedModelAdelePointTopology K S X,
      numberFieldFixedModelAdelePointTopology K S Y]
      (fun p : NumberFieldFixedModelAdelePoints K S X =>
        (p ≫ f : NumberFieldFixedModelAdelePoints K S Y)) := by
  let R : Type u := ((S : Set (FinitePlace K)).integer K)
  let D := numberFieldAdeleLevelOverDiagram K S
  let c := numberFieldAdeleOverCocone K S
  let τX := numberFieldFixedModelStageTopology K S X
  let τY := numberFieldFixedModelStageTopology K S Y
  let : TopologicalSpace (RingPoint R X c.pt) := numberFieldFixedModelAdelePointTopology K S X
  let : TopologicalSpace (RingPoint R Y c.pt) := numberFieldFixedModelAdelePointTopology K S Y
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Y
  apply (ringPointCoconeTopology_continuous_iff R D X τX c (Y := RingPoint R Y c.pt)
    (fun p : RingPoint R X c.pt => (p ≫ f : RingPoint R Y c.pt))).2
  intro T
  let : TopologicalSpace (RingPoint R X (D.obj T)) := τX T
  let : TopologicalSpace (RingPoint R Y (D.obj T)) := τY T
  have hi := ringPointCoconeTopology_continuous_ι R D Y τY c T
  have hf := numberFieldFixedModelStage_continuous K S f T
  refine (hi.comp hf).congr ?_
  intro p
  exact (Category.assoc _ _ _).symm

/-- Actual model isomorphisms induce homeomorphisms for the original final topologies. -/
def numberFieldFixedModelIsoHomeomorph (e : X ≅ Y) :
    @Homeomorph (NumberFieldFixedModelAdelePoints K S X)
      (NumberFieldFixedModelAdelePoints K S Y)
      (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S Y) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Y
  exact {
  toEquiv :=
    { toFun := fun p => p ≫ e.hom
      invFun := fun p => p ≫ e.inv
      left_inv := by
        intro p
        exact (Category.assoc p e.hom e.inv).trans
          ((congrArg (fun a => p ≫ a) e.hom_inv_id).trans (Category.comp_id p))
      right_inv := by
        intro p
        exact (Category.assoc p e.inv e.hom).trans
          ((congrArg (fun a => p ≫ a) e.inv_hom_id).trans (Category.comp_id p)) }
  continuous_toFun := numberFieldFixedModelAdele_continuous K S e.hom
  continuous_invFun := numberFieldFixedModelAdele_continuous K S e.inv }

end NumberField

/-- The exact functoriality target for actual full-adele model points. -/
theorem adelicFixedModelFunctoriality : AdelicFixedModelFunctorialityStatement.{u} :=
  ⟨fun k F _ _ _ S _ _ f => curvePlaceFixedModelAdele_continuous k F S f,
    fun K _ _ S _ _ f => numberFieldFixedModelAdele_continuous K S f⟩

end Langlands.Global
