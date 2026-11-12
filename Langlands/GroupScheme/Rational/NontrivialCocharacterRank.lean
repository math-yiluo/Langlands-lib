import Langlands.GroupScheme.Rational.SplitTorusImage

/-! # A nontrivial cocharacter gives positive split rank -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual homomorphism from the multiplicative group that is not the
constant identity homomorphism exists over the base field. -/
def HasNontrivialCocharacter (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, χ ≠ 0

/-- A nontrivial cocharacter into an affine group has a positive-dimensional
closed split-torus image, so the split rank is at least one. -/
theorem HasNontrivialCocharacter.one_le_splitRank
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : HasNontrivialCocharacter G) : 1 ≤ splitRank G := by
  obtain ⟨χ, hχ⟩ := hG
  obtain ⟨T, π, i, hi, hfac, _⟩ :=
    isSplitTorus_gm.exists_factor_isSplitSubtorus χ
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.1
  have : Finite I := hI
  have hcard : Nat.card I ≠ 0 := by
    intro hz
    have : IsEmpty I :=
      (Nat.card_eq_zero.mp hz).resolve_right (not_infinite_iff_finite.mpr inferInstance)
    have hzero : e.inv ≫ i = 0 :=
      (splitTorus.subsingleton_hom_of_isEmpty I G).elim _ _
    have hi0 : i = 0 := by
      rw [← e.hom_inv_id_assoc i, hzero, Limits.comp_zero]
    apply hχ
    rw [← hfac, hi0, Limits.comp_zero]
  have hone : (1 : ℕ∞) ≤ (Nat.card I : ℕ∞) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcard
  exact hone.trans (hi.card_le_splitRank I e)

/-- The version with the cocharacter and its nontriviality supplied
separately. No closed-immersion hypothesis on the cocharacter is needed. -/
theorem one_le_splitRank_of_cocharacter_ne_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (hχ : χ ≠ 0) :
    1 ≤ splitRank G :=
  HasNontrivialCocharacter.one_le_splitRank ⟨χ, hχ⟩

/-- An affine anisotropic group has only trivial base-field cocharacters. -/
theorem IsAnisotropic.cocharacter_eq_zero
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsAnisotropic G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : χ = 0 := by
  by_contra hχ
  have h := one_le_splitRank_of_cocharacter_ne_zero χ hχ
  rw [show splitRank G = 0 from hG] at h
  exact absurd h (by simp)

end Langlands.GroupScheme
