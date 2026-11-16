import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Specialization from algebraically closed valuative tests -/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry IsLocalRing

/-- Existence of lifts for valuation subrings of algebraically closed fields. -/
def HasAlgClosedValuationLifts {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
      (b : Spec ↧A ⟶ Y) (a : Spec ↧K ⟶ X),
    a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b →
      ∃ l : Spec ↧A ⟶ X,
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ l = a ∧ l ≫ f = b

set_option backward.isDefEq.respectTransparency.types false in
/-- Algebraically closed valuative tests suffice to lift specializations. -/
theorem specializingMap_of_algClosed_valuation_lifts {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : HasAlgClosedValuationLifts f) : SpecializingMap f := by
  intro x' y h
  let K := AlgebraicClosure (X.residueField x')
  let ι : X.residueField x' ⟶ ↧K :=
    CommRingCat.ofHom (algebraMap (X.residueField x') K)
  let stalk_y_to_K : Y.presheaf.stalk y ⟶ ↧K :=
    Y.presheaf.stalkSpecializes h ≫ f.stalkMap x' ≫ X.residue x' ≫ ι
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing stalk_y_to_K.hom
  let stalk_y_to_A : Y.presheaf.stalk y ⟶ ↧A :=
    CommRingCat.ofHom (stalk_y_to_K.hom.codRestrict A.toSubring hA)
  let a : Spec ↧K ⟶ X := Spec.map ι ≫ X.fromSpecResidueField x'
  let b : Spec ↧A ⟶ Y := Spec.map stalk_y_to_A ≫ Y.fromSpecStalk y
  have w : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ b := by
    dsimp only [a, b]
    rw [Category.assoc, Scheme.fromSpecResidueField, Category.assoc,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨l, hl₁, hl₂⟩ := H K A b a w
  refine ⟨l (closedPoint A), ?_, ?_⟩
  · have hx : l (Spec.map (CommRingCat.ofHom (algebraMap A K)) (closedPoint K)) = x' := by
      rw [← Scheme.Hom.comp_apply, hl₁]
      simp [a, Scheme.fromSpecResidueField_apply]
    exact (specializes_of_eq hx.symm).trans ((specializes_closedPoint _).map l.continuous)
  · rw [← Scheme.Hom.comp_apply, hl₂]
    simp only [b, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    have : Spec.map stalk_y_to_A (closedPoint A) = closedPoint (Y.presheaf.stalk y) :=
      comap_closedPoint (S := A) (stalk_y_to_K.hom.codRestrict A.toSubring hA)
    rw [this, Y.fromSpecStalk_closedPoint]

end Langlands.AlgebraicGeometry
