import Langlands.AlgebraicGeometry.Picard.GenericFractionField
import Langlands.AlgebraicGeometry.Picard.GenericSectionRestriction

/-! # Section restriction to a chosen fraction field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

variable (R : CommRingCat.{u}) [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (p : X ⟶ Spec R)

/-- Restrict an actual section along the given fraction-field algebra map. -/
def fractionFieldSectionRestriction :
    {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)} →
      {sK : Spec (CommRingCat.of K) ⟶ X //
        sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
  fun s => ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.val, by
    rw [Category.assoc, s.property]
    exact Category.comp_id _⟩

/-- Transport actual generic residue-field maps to maps from the chosen
fraction field, with their equations over the original spectrum. -/
def fractionFieldGenericSectionEquiv :
    {sη : Spec ((Spec R).residueField (genericPoint (Spec R))) ⟶ X //
      sη ≫ p = (Spec R).fromSpecResidueField (genericPoint (Spec R))} ≃
    {sK : Spec (CommRingCat.of K) ⟶ X //
      sK ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R K))} :=
  { toFun := fun sη => ⟨(fractionFieldGenericPointIso R K).hom ≫ sη.val, by
      rw [Category.assoc, sη.property,
        fractionFieldGenericPointIso_hom_fromSpecResidueField]⟩
    invFun := fun sK => ⟨(fractionFieldGenericPointIso R K).inv ≫ sK.val, by
      rw [Category.assoc, sK.property,
        ← fractionFieldGenericPointIso_hom_fromSpecResidueField R K,
        Iso.inv_hom_id_assoc]⟩
    left_inv := fun sη => Subtype.ext (by simp)
    right_inv := fun sK => Subtype.ext (by simp) }

/-- The transport equivalence takes canonical generic restriction to
restriction along the specified fraction-field algebra map. -/
@[simp]
theorem fractionFieldGenericSectionEquiv_restriction
    (s : {s : Spec R ⟶ X // s ≫ p = 𝟙 (Spec R)}) :
    fractionFieldGenericSectionEquiv R K p (genericSectionRestriction p s) =
      fractionFieldSectionRestriction R K p s := by
  apply Subtype.ext
  change (fractionFieldGenericPointIso R K).hom ≫
      ((Spec R).fromSpecResidueField (genericPoint (Spec R)) ≫ s.val) =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s.val
  rw [← Category.assoc,
    fractionFieldGenericPointIso_hom_fromSpecResidueField]

/-- Chosen-fraction-field restriction is injective for separated morphisms. -/
theorem fractionFieldSectionRestriction_injective [IsSeparated p] :
    Function.Injective (fractionFieldSectionRestriction R K p) := by
  intro s t h
  apply genericSectionRestriction_injective p
  apply (fractionFieldGenericSectionEquiv R K p).injective
  simpa only [fractionFieldGenericSectionEquiv_restriction] using h

/-- Existence of extensions is unchanged by the canonical replacement of
the generic residue field by any chosen fraction field. -/
theorem fractionFieldSectionRestriction_surjective_iff :
    Function.Surjective (fractionFieldSectionRestriction R K p) ↔
      Function.Surjective (genericSectionRestriction p) := by
  constructor
  · intro h sη
    obtain ⟨s, hs⟩ := h (fractionFieldGenericSectionEquiv R K p sη)
    refine ⟨s, (fractionFieldGenericSectionEquiv R K p).injective ?_⟩
    simpa only [fractionFieldGenericSectionEquiv_restriction] using hs
  · intro h sK
    obtain ⟨s, hs⟩ := h ((fractionFieldGenericSectionEquiv R K p).symm sK)
    refine ⟨s, ?_⟩
    rw [← fractionFieldGenericSectionEquiv_restriction, hs, Equiv.apply_symm_apply]

end Langlands.AlgebraicGeometry
