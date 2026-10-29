import Langlands.CategoryTheory.Renard.SubobjectComplementComparisonStatements
import Langlands.CategoryTheory.RenardNoetherIsomorphisms

/-!
# Proof of the canonical subobject-complement comparison

Proof of `Langlands.Renard.SubobjectComplementComparisonStatement` in an
arbitrary abelian category. The comparison is internal, motivated by Renard 2026
A.VI.2(9) and A.VII(iii). The direction from lattice complements to the
canonical coproduct map reuses `complementarySubobjectsSum`.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The actual canonical coproduct comparison detects lattice complements. -/
theorem canonicalSubobjectComplement (C : Type u) [Category.{v} C] [Abelian C] :
    CanonicalSubobjectComplementStatement C := by
  intro X P Q
  constructor
  · intro h
    let f := coprod.desc P.arrow Q.arrow
    have : IsIso f := h
    let p : X ⟶ (P : C) :=
      inv f ≫ coprod.desc (𝟙 (P : C)) (0 : (Q : C) ⟶ (P : C))
    have hPi : P.arrow ≫ inv f = coprod.inl := by
      rw [← cancel_mono f]
      simp [Category.assoc, f]
    have hQi : Q.arrow ≫ inv f = coprod.inr := by
      rw [← cancel_mono f]
      simp [Category.assoc, f]
    have hp : P.arrow ≫ p = 𝟙 _ := by
      dsimp only [p]
      rw [← Category.assoc, hPi, coprod.inl_desc]
    have hq : Q.arrow ≫ p = 0 := by
      dsimp only [p]
      rw [← Category.assoc, hQi, coprod.inr_desc]
    have hfac : Subobject.ofLE (P ⊓ Q) P inf_le_left ≫ P.arrow =
        Subobject.ofLE (P ⊓ Q) Q inf_le_right ≫ Q.arrow := by
      simp
    have hz : Subobject.ofLE (P ⊓ Q) P inf_le_left = 0 := by
      calc
        Subobject.ofLE (P ⊓ Q) P inf_le_left =
            Subobject.ofLE (P ⊓ Q) P inf_le_left ≫ (P.arrow ≫ p) := by
          rw [hp, Category.comp_id]
        _ = Subobject.ofLE (P ⊓ Q) Q inf_le_right ≫ Q.arrow ≫ p := by
          rw [← Category.assoc, hfac, Category.assoc]
        _ = 0 := by rw [hq, comp_zero]
    have harrow : (P ⊓ Q).arrow = 0 := by
      rw [← Subobject.ofLE_arrow (inf_le_left : P ⊓ Q ≤ P), hz, zero_comp]
    have hinf : P ⊓ Q = ⊥ :=
      (Subobject.mk_arrow _).symm.trans (Subobject.mk_eq_bot_iff_zero.mpr harrow)
    let g := coprod.desc (Subobject.ofLE P (P ⊔ Q) le_sup_left)
      (Subobject.ofLE Q (P ⊔ Q) le_sup_right)
    have hgf : g ≫ (P ⊔ Q).arrow = f := by
      ext <;> simp [g, f]
    have : Epi (g ≫ (P ⊔ Q).arrow) := by
      rw [hgf]
      infer_instance
    have : Epi (P ⊔ Q).arrow := epi_of_epi g (P ⊔ Q).arrow
    have := isIso_of_mono_of_epi (P ⊔ Q).arrow
    exact ⟨hinf, Subobject.eq_top_of_isIso_arrow _⟩
  · rintro ⟨hinf, hsup⟩
    exact complementarySubobjectsSum C X P Q hinf hsup

/-- The canonical complement predicate is the actual complemented-lattice property. -/
theorem everySubobjectComplementedLattice
    (C : Type u) [Category.{v} C] [Abelian C] :
    EverySubobjectComplementedLatticeStatement C := by
  intro X
  rw [complementedLattice_iff]
  change (∀ P : Subobject X, ∃ Q : Subobject X, IsIso (coprod.desc P.arrow Q.arrow)) ↔ _
  simp_rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  exact forall_congr' fun P =>
    exists_congr fun Q => canonicalSubobjectComplement C X P Q

/-- The exact internal subobject complement comparison family. -/
theorem subobjectComplementComparison
    (C : Type u) [Category.{v} C] [Abelian C] :
    SubobjectComplementComparisonStatement C :=
  ⟨canonicalSubobjectComplement C, everySubobjectComplementedLattice C⟩

end Langlands.Renard
