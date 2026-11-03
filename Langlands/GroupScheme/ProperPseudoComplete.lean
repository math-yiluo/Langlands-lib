import Langlands.GroupScheme.PseudoComplete
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Proper schemes are pseudo-complete -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace PseudoComplete

/-- A fraction-field point of a proper relative scheme extends over every DVR. -/
theorem exists_extension_of_isProper
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [IsDiscreteValuationRing R]
    (x : algebraSpec k (FractionRing R) ⟶ X) :
    ∃ xR : algebraSpec k R ⟶ X, genericPoint (k := k) R ≫ xR = x := by
  have hVC : ValuativeCriterion.Existence X.hom := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) X.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let sq : ValuativeCommSq X.hom :=
    { R := R
      K := FractionRing R
      i₁ := x.left
      i₂ := (algebraSpec k R).hom
      commSq := ⟨by
        change x.left ≫ X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
            (algebraSpec k R).hom
        rw [Over.w x]
        exact (Over.w (genericPoint (k := k) R)).symm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (hVC sq).exists_lift
  refine ⟨Over.homMk l hl₂, ?_⟩
  exact Over.OverMorphism.ext hl₁

/-- The chosen extension of a fraction-field point to a DVR for a proper scheme. -/
def properDVRLift
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [IsDiscreteValuationRing R]
    (x : algebraSpec k (FractionRing R) ⟶ X) : algebraSpec k R ⟶ X :=
  (exists_extension_of_isProper X R x).choose

/-- The chosen extension restricts to the supplied fraction-field point. -/
@[simp]
theorem genericPoint_properDVRLift
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [IsDiscreteValuationRing R]
    (x : algebraSpec k (FractionRing R) ⟶ X) :
    genericPoint (k := k) R ≫ properDVRLift X R x = x :=
  (exists_extension_of_isProper X R x).choose_spec

/-- A proper relative scheme has the actual restricted DVR extension property. -/
theorem hasDVRLifting_of_isProper
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] : HasDVRLifting X := by
  intro R _ _ _ _ _ x
  exact ⟨properDVRLift X R x, genericPoint_properDVRLift X R x⟩

end PseudoComplete

/-- Properness implies the published pseudo-completeness predicate over every field. -/
theorem isPseudoComplete_of_isProper
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] : IsPseudoComplete X := by
  exact ⟨inferInstance, inferInstance, inferInstance,
    PseudoComplete.hasDVRLifting_of_isProper X⟩

end Langlands.GroupScheme
