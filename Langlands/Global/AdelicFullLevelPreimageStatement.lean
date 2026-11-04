import Langlands.Global.AdelicFixedModelCocone
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Full-adele preimages of actual arithmetic-level model points -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- Proper model morphisms pull the image of a curve-place level back to that level. -/
def CurvePlaceFullLevelPreimageStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    (S : Finset (AlgebraicCurve.Place k F)),
    let ι : curvePlaceAdeleLevel k F S →ₐ[curvePlaceSIntegers k F S]
        curvePlaceAdeleOver k F S :=
      { toRingHom := (curvePlaceAdeleLevel k F S).subtype, commutes' := fun _ => rfl }
    ∀ (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
      [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left],
      (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
        (p ≫ f : CurvePlaceFixedModelAdelePoints k F S Y)) ⁻¹'
          Set.range (RingPoint.changeRing (X := Y) ι) =
        Set.range (RingPoint.changeRing (X := X) ι)

/-- Proper model morphisms pull the image of a number-field level back to that level. -/
def NumberFieldFullLevelPreimageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K)),
    let ι : numberFieldAdeleLevel K S →ₐ[(S : Set (FinitePlace K)).integer K]
        numberFieldAdeleOver K S :=
      { toRingHom := (numberFieldAdeleLevel K S).subtype, commutes' := fun _ => rfl }
    ∀ (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
      [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left],
      (fun p : NumberFieldFixedModelAdelePoints K S X =>
        (p ≫ f : NumberFieldFixedModelAdelePoints K S Y)) ⁻¹'
          Set.range (RingPoint.changeRing (X := Y) ι) =
        Set.range (RingPoint.changeRing (X := X) ι)

/-- Both actual-arithmetic full-level preimage assertions in arbitrary common universe. -/
def AdelicFullLevelPreimageStatement : Prop :=
  CurvePlaceFullLevelPreimageStatement.{u} ∧ NumberFieldFullLevelPreimageStatement.{u}

end Langlands.Global
