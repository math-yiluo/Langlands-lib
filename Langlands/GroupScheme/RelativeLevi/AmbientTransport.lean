import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalConstructions
import Langlands.GroupScheme.Rational.LeviAmbientTransport

/-! # Ambient isomorphisms of relative Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {L P P' : GroupScheme S} {l : L ⟶ P}

/-- An ambient group-scheme isomorphism preserves the relative Levi predicate,
including its actual Levi-first multiplication isomorphism. -/
theorem IsRelativeLeviSubgroup.comp_iso
    (hl : IsRelativeLeviSubgroup l) (e : P ≅ P') :
    IsRelativeLeviSubgroup (l ≫ e.hom) := by
  refine ⟨hl.isClosedSubgroup.comp_iso e, hl.smooth, ?_⟩
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  refine ⟨U, r ≫ e.hom, hr.comp_iso e, ?_⟩
  rw [subgroupMultiplication_postcomp]
  let : IsIso (subgroupMultiplication l r) := hmul
  infer_instance

/-- The relative Levi predicate is invariant under an isomorphism of the
ambient group scheme. -/
theorem IsRelativeLeviSubgroup.comp_iso_iff (e : P ≅ P') :
    IsRelativeLeviSubgroup (l ≫ e.hom) ↔ IsRelativeLeviSubgroup l := by
  constructor
  · intro hl
    simpa only [Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id] using
      hl.comp_iso e.symm
  · intro hl
    exact hl.comp_iso e

/-- Postcomposition with an ambient isomorphism identifies the relative Levi
embeddings of a fixed group scheme into the two ambient group schemes. -/
def RelativeLevi.ambientTransportEquiv (L : GroupScheme S) (e : P ≅ P') :
    {l : L ⟶ P // IsRelativeLeviSubgroup l} ≃
      {l' : L ⟶ P' // IsRelativeLeviSubgroup l'} where
  toFun l := ⟨l.1 ≫ e.hom, l.2.comp_iso e⟩
  invFun l' := ⟨l'.1 ≫ e.inv, l'.2.comp_iso e.symm⟩
  left_inv l := by
    apply Subtype.ext
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv l' := by
    apply Subtype.ext
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme
