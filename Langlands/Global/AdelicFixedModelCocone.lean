import Langlands.Global.AdelicFixedModelSystem

/-! # The actual full-adele cocone of a fixed arithmetic model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Enlarge any finite set to one containing the fixed initial set. -/
def adelicLevelIndexEnlarge {ι : Type u} (S T : Finset ι) : AdelicLevelIndexAbove S := by
  classical
  exact ⟨S ∪ T, Finset.subset_union_left⟩

/-- Enlarging preserves inclusion of the variable finite set. -/
theorem adelicLevelIndexEnlarge_mono {ι : Type u} (S : Finset ι) :
    Monotone (adelicLevelIndexEnlarge S) := by
  classical
  intro T U h
  exact Finset.union_subset_union (Finset.Subset.refl S) h

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))

/-- The actual full adele ring with the original fixed integer-base action. -/
def curvePlaceAdeleOver : CommAlgCat.{u} (curvePlaceSIntegers k F S) := by
  letI : Algebra (curvePlaceSIntegers k F S) (CurvePlaceAdeleRing k F) :=
    ((curvePlaceAdeleLevel k F S).subtype.comp (curvePlaceAdeleLevelDiagonal k F S)).toAlgebra
  exact CommAlgCat.of (curvePlaceSIntegers k F S) (CurvePlaceAdeleRing k F)

/-- The literal inclusion of a level into full adeles as a fixed-base algebra map. -/
def curvePlaceAdeleLevelOverι (T : AdelicLevelIndexAbove S) :
    curvePlaceAdeleLevelOver k F S T ⟶ curvePlaceAdeleOver k F S := by
  let f : curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F S]
      curvePlaceAdeleOver k F S :=
    { toRingHom := (curvePlaceAdeleLevel k F T.val).subtype
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat (curvePlaceSIntegers k F S)) f

/-- The canonical cocone whose point is the actual full adele algebra. -/
def curvePlaceAdeleOverCocone : Cocone (curvePlaceAdeleLevelOverDiagram k F S) where
  pt := curvePlaceAdeleOver k F S
  ι :=
    { app := curvePlaceAdeleLevelOverι k F S
      naturality := by intro T U h; ext a; rfl }

variable (X : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- Actual points of the initial model on the full adele ring. -/
abbrev CurvePlaceFixedModelAdelePoints :=
  RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleOver k F S)

/-- The canonical map from stage-point classes to actual full-adele model points. -/
def curvePlaceFixedModelPointComparison :
    CurvePlaceFixedModelPointColimit k F S X → CurvePlaceFixedModelAdelePoints k F S X :=
  ringPointColimitMap (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceAdeleOverCocone k F S)

/-- The full-adele point topology is final from the original arithmetic model stages. -/
@[instance_reducible]
def curvePlaceFixedModelAdelePointTopology :
    TopologicalSpace (CurvePlaceFixedModelAdelePoints k F S X) :=
  ringPointCoconeTopology (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceFixedModelStageTopology k F S X)
    (curvePlaceAdeleOverCocone k F S)

/-- On a stage, the comparison uses exactly the spectrum of the literal inclusion. -/
@[simp]
theorem curvePlaceFixedModelPointComparison_ι_left (T : AdelicLevelIndexAbove S)
    (p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    (curvePlaceFixedModelPointComparison k F S X
      (ringPointColimitι (curvePlaceSIntegers k F S)
        (curvePlaceAdeleLevelOverDiagram k F S) X T p)).left =
      Spec.map (CommRingCat.ofHom (curvePlaceAdeleLevel k F T.val).subtype) ≫ p.left := rfl

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))

/-- The actual full adele ring with the original fixed integer-base action. -/
def numberFieldAdeleOver : CommAlgCat.{u} (((S : Set (FinitePlace K)).integer K)) := by
  letI : Algebra (((S : Set (FinitePlace K)).integer K)) (Adeles K) :=
    ((numberFieldAdeleLevel K S).subtype.comp (numberFieldAdeleLevelDiagonal K S)).toAlgebra
  exact CommAlgCat.of (((S : Set (FinitePlace K)).integer K)) (Adeles K)

/-- The literal inclusion of a level into full adeles as a fixed-base algebra map. -/
def numberFieldAdeleLevelOverι (T : AdelicLevelIndexAbove S) :
    numberFieldAdeleLevelOver K S T ⟶ numberFieldAdeleOver K S := by
  let f : numberFieldAdeleLevelOver K S T →ₐ[((S : Set (FinitePlace K)).integer K)]
      numberFieldAdeleOver K S :=
    { toRingHom := (numberFieldAdeleLevel K T.val).subtype
      commutes' := fun _ => rfl }
  exact ConcreteCategory.ofHom (C := CommAlgCat (((S : Set (FinitePlace K)).integer K))) f

/-- The canonical cocone whose point is the actual full adele algebra. -/
def numberFieldAdeleOverCocone : Cocone (numberFieldAdeleLevelOverDiagram K S) where
  pt := numberFieldAdeleOver K S
  ι :=
    { app := numberFieldAdeleLevelOverι K S
      naturality := by intro T U h; ext a; rfl }

variable (X : Over (Spec (CommRingCat.of (((S : Set (FinitePlace K)).integer K)))))

/-- Actual points of the initial model on the full adele ring. -/
abbrev NumberFieldFixedModelAdelePoints :=
  RingPoint (((S : Set (FinitePlace K)).integer K)) X (numberFieldAdeleOver K S)

/-- The canonical map from stage-point classes to actual full-adele model points. -/
def numberFieldFixedModelPointComparison :
    NumberFieldFixedModelPointColimit K S X → NumberFieldFixedModelAdelePoints K S X :=
  ringPointColimitMap (((S : Set (FinitePlace K)).integer K))
    (numberFieldAdeleLevelOverDiagram K S) X (numberFieldAdeleOverCocone K S)

/-- The full-adele point topology is final from the original arithmetic model stages. -/
@[instance_reducible]
def numberFieldFixedModelAdelePointTopology :
    TopologicalSpace (NumberFieldFixedModelAdelePoints K S X) :=
  ringPointCoconeTopology (((S : Set (FinitePlace K)).integer K))
    (numberFieldAdeleLevelOverDiagram K S) X (numberFieldFixedModelStageTopology K S X)
    (numberFieldAdeleOverCocone K S)

/-- On a stage, the comparison uses exactly the spectrum of the literal inclusion. -/
@[simp]
theorem numberFieldFixedModelPointComparison_ι_left (T : AdelicLevelIndexAbove S)
    (p : RingPoint (((S : Set (FinitePlace K)).integer K)) X (numberFieldAdeleLevelOver K S T)) :
    (numberFieldFixedModelPointComparison K S X
      (ringPointColimitι (((S : Set (FinitePlace K)).integer K))
        (numberFieldAdeleLevelOverDiagram K S) X T p)).left =
      Spec.map (CommRingCat.ofHom (numberFieldAdeleLevel K T.val).subtype) ≫ p.left := rfl

end NumberField

end Langlands.Global
