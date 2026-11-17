import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Ring.Multiset

/-! # Multiplicative polynomial functions and roots

This module contains the two polynomial lemmas of Milne's proof of Proposition 12.9
(*Abelian Varieties*, Lemmas 12.10 and 12.11), in the form used later.

* `eq_prod_eval_roots`: a function `Φ` on polynomials over an algebraically closed field that
  is multiplicative in bounded degree, equals `c ↦ c ^ m` on constants and `x ↦ Q(x)` on the
  linear polynomials `X - x`, with `Q` monic of even degree `m`, is `F ↦ ∏ F(q)` over the
  roots `q` of `Q`.
* `rootMultiplicity_zero_prod`: the order at `0` of `∏ (t + f(q))` is the number of `q` with
  `f(q) = 0`.
* `eq_of_rootCount_eq`: two monic polynomials over a field `K` agree if, for every monic
  irreducible `π` over `K`, they have the same number of roots in an algebraically closed
  algebraic extension at which `π` vanishes.
-/

noncomputable section

open Polynomial

namespace Langlands.Algebra.DegreeDeterminant

section Product

variable {L : Type*} [Field L]

/-- A function multiplicative in bounded degree on products of linear factors. -/
theorem map_C_mul_prod_X_sub_C (B m : ℕ) (Φ : L[X] → L)
    (hmul : ∀ F G : L[X], F.natDegree ≤ B → G.natDegree ≤ B → Φ (F * G) = Φ F * Φ G)
    (hC : ∀ c : L, Φ (C c) = c ^ m) (Q : L[X]) (hlin : ∀ x : L, Φ (X - C x) = Q.eval x) :
    ∀ (s : Multiset L), Multiset.card s ≤ B → ∀ c : L,
      Φ (C c * (s.map fun r => X - C r).prod) = c ^ m * (s.map fun r => Q.eval r).prod := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ c; simp [hC]
  | cons r s ih =>
    intro hs c
    rw [Multiset.card_cons] at hs
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      mul_left_comm, hmul, hlin, ih (by omega) c]
    · ring
    · rw [natDegree_X_sub_C]; omega
    · calc natDegree (C c * (s.map fun r => X - C r).prod)
          ≤ natDegree (s.map fun r => X - C r).prod := natDegree_C_mul_le _ _
        _ = Multiset.card s := natDegree_multiset_prod_X_sub_C_eq_card s
        _ ≤ B := by omega

/-- Milne's Lemma 12.11 in the form used here. -/
theorem eq_prod_eval_roots [IsAlgClosed L] (B m : ℕ) (hm : Even m) (Φ : L[X] → L)
    (hmul : ∀ F G : L[X], F.natDegree ≤ B → G.natDegree ≤ B → Φ (F * G) = Φ F * Φ G)
    (hC : ∀ c : L, Φ (C c) = c ^ m) (Q : L[X]) (hQ : Q.Monic) (hQdeg : Q.natDegree = m)
    (hlin : ∀ x : L, Φ (X - C x) = Q.eval x) (F : L[X]) (hF : F.natDegree ≤ B) :
    Φ F = (Q.roots.map fun q => F.eval q).prod := by
  have hFroots : Multiset.card F.roots = F.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hQroots : Multiset.card Q.roots = m := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQdeg]
  have hFfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hFroots
  have hQfac := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ (by rw [hQroots, hQdeg])
  have hQe : ∀ r, Q.eval r = (Q.roots.map fun q => r - q).prod := by
    intro r
    conv_lhs => rw [← hQfac]
    rw [eval_multiset_prod, Multiset.map_map]
    simp
  have hFe : ∀ q, F.eval q = F.leadingCoeff * (F.roots.map fun r => q - r).prod := by
    intro q
    conv_lhs => rw [← hFfac]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  have hswap : ∀ r, (Q.roots.map fun q => r - q).prod = (Q.roots.map fun q => q - r).prod := by
    intro r
    have h : (Q.roots.map fun q => r - q) = (Q.roots.map fun q => q - r).map Neg.neg := by
      rw [Multiset.map_map]
      congr 1
      funext q
      simp
    rw [h, Multiset.prod_map_neg, Multiset.card_map, hQroots, hm.neg_one_pow, one_mul]
  conv_lhs => rw [← hFfac]
  rw [map_C_mul_prod_X_sub_C B m Φ hmul hC Q hlin F.roots (hFroots ▸ hF) F.leadingCoeff]
  simp_rw [hQe, hswap, hFe]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hQroots,
    Multiset.prod_map_prod_map]

end Product

/-- The order at `0` of `∏ (X + f(q))` is the number of `q` with `f(q) = 0`. -/
theorem rootMultiplicity_zero_prod {L : Type*} [Field L] [DecidableEq L] (s : Multiset L)
    (f : L → L) :
    rootMultiplicity 0 (s.map fun q => X + C (f q)).prod =
      Multiset.card (s.filter fun q => f q = 0) := by
  have h : (s.map fun q => X + C (f q)) = (s.map fun q => -f q).map fun a => X - C a := by
    rw [Multiset.map_map]
    congr 1
    funext q
    simp [sub_eq_add_neg]
  rw [h, ← count_roots, roots_multiset_prod_X_sub_C, Multiset.count_map]
  congr 1
  apply Multiset.filter_congr
  intro q _
  rw [eq_comm, neg_eq_zero]

section Count

variable (L : Type*) {K : Type*} [Field K] [Field L] [Algebra K L]

open Classical in
/-- The number of roots in `L`, with multiplicity, of `F` at which `π` vanishes. -/
def rootCount (F π : K[X]) : ℕ :=
  Multiset.card ((F.map (algebraMap K L)).roots.filter fun q => aeval q π = 0)

theorem rootCount_mul {F G : K[X]} (hF : F ≠ 0) (hG : G ≠ 0) (π : K[X]) :
    rootCount L (F * G) π = rootCount L F π + rootCount L G π := by
  classical
  unfold rootCount
  rw [Polynomial.map_mul, roots_mul, Multiset.filter_add, Multiset.card_add]
  rw [← Polynomial.map_mul]
  exact Polynomial.map_ne_zero (mul_ne_zero hF hG)

theorem rootCount_one (π : K[X]) : rootCount L (1 : K[X]) π = 0 := by
  classical
  unfold rootCount
  rw [Polynomial.map_one, roots_one]
  rfl

variable [IsAlgClosed L] [Algebra.IsAlgebraic K L]

/-- A nonconstant polynomial has a root in `L`; its minimal polynomial divides it and is
counted at least once. -/
theorem exists_minpoly_dvd {F : K[X]} (hF : F ≠ 0) (hdeg : 0 < F.natDegree) :
    ∃ θ : L, minpoly K θ ∣ F ∧ (minpoly K θ).Monic ∧ Irreducible (minpoly K θ) ∧
      0 < (minpoly K θ).natDegree ∧ 1 ≤ rootCount L F (minpoly K θ) := by
  classical
  have hmap : F.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hF
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root (F.map (algebraMap K L))
    (by rw [degree_map]; exact (natDegree_pos_iff_degree_pos.mp hdeg).ne')
  have hint : IsIntegral K θ := Algebra.IsIntegral.isIntegral θ
  have hFθ : aeval θ F = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  refine ⟨θ, minpoly.dvd K θ hFθ, minpoly.monic hint, minpoly.irreducible hint,
    minpoly.natDegree_pos hint, ?_⟩
  unfold rootCount
  exact Multiset.card_pos_iff_exists_mem.mpr
    ⟨θ, Multiset.mem_filter.mpr ⟨(mem_roots hmap).mpr hθ, minpoly.aeval K θ⟩⟩

omit [IsAlgClosed L] [Algebra.IsAlgebraic K L] in
/-- If `π` is monic irreducible and vanishes at a root of `F` in `L`, then `π` divides `F`. -/
theorem dvd_of_rootCount_pos {F π : K[X]} (hF : F ≠ 0) (hπ : π.Monic) (hirr : Irreducible π)
    (h : 1 ≤ rootCount L F π) : π ∣ F := by
  classical
  unfold rootCount at h
  obtain ⟨θ, hθ⟩ := Multiset.card_pos_iff_exists_mem.mp h
  rw [Multiset.mem_filter] at hθ
  have hmap : F.map (algebraMap K L) ≠ 0 := Polynomial.map_ne_zero hF
  have hFθ : aeval θ F = 0 := by
    rw [aeval_def, eval₂_eq_eval_map]
    exact (mem_roots hmap).mp hθ.1
  rw [minpoly.eq_of_irreducible_of_monic hirr hθ.2 hπ]
  exact minpoly.dvd K θ hFθ

/-- Milne's Lemma 12.10 in root-count form: two monic polynomials of degree at most `B`
with the same root counts for all monic irreducible `π` of degree at most `B` are equal. -/
theorem eq_of_rootCount_eq (B : ℕ) : ∀ (d : ℕ) (Q χ : K[X]), Q.natDegree = d → Q.Monic →
    χ.Monic → Q.natDegree ≤ B → χ.natDegree ≤ B →
    (∀ π : K[X], π.Monic → Irreducible π → π.natDegree ≤ B →
      rootCount L Q π = rootCount L χ π) → Q = χ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro Q χ hd hQ hχ hQB hχB hcount
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · have hQ1 : Q = 1 := eq_one_of_monic_natDegree_zero hQ hd
      rcases Nat.eq_zero_or_pos χ.natDegree with hχ0 | hχpos
      · rw [hQ1, eq_one_of_monic_natDegree_zero hχ hχ0]
      · obtain ⟨θ, hdvd, hmon, hirr, -, hcnt⟩ := exists_minpoly_dvd L hχ.ne_zero hχpos
        have hle : (minpoly K θ).natDegree ≤ B :=
          (natDegree_le_of_dvd hdvd hχ.ne_zero).trans hχB
        have := hcount _ hmon hirr hle
        rw [hQ1, rootCount_one] at this
        omega
    · obtain ⟨θ, hdvd, hmon, hirr, hdegπ, hcnt⟩ :=
        exists_minpoly_dvd L hQ.ne_zero (hd ▸ hpos)
      set π := minpoly K θ
      have hle : π.natDegree ≤ B := (natDegree_le_of_dvd hdvd hQ.ne_zero).trans hQB
      have hcntχ : 1 ≤ rootCount L χ π := (hcount π hmon hirr hle) ▸ hcnt
      have hdvdχ : π ∣ χ := dvd_of_rootCount_pos L hχ.ne_zero hmon hirr hcntχ
      obtain ⟨Q₁, rfl⟩ := hdvd
      obtain ⟨χ₁, rfl⟩ := hdvdχ
      have hQ₁ : Q₁.Monic := hmon.of_mul_monic_left hQ
      have hχ₁ : χ₁.Monic := hmon.of_mul_monic_left hχ
      have hdeg₁ : (π * Q₁).natDegree = π.natDegree + Q₁.natDegree := hmon.natDegree_mul hQ₁
      have hdegχ₁ : (π * χ₁).natDegree = π.natDegree + χ₁.natDegree := hmon.natDegree_mul hχ₁
      have := ih Q₁.natDegree (by omega) Q₁ χ₁ rfl hQ₁ hχ₁ (by omega) (by omega)
        (fun ρ hρ hirrρ hρB => by
          have h := hcount ρ hρ hirrρ hρB
          rw [rootCount_mul L hmon.ne_zero hQ₁.ne_zero,
            rootCount_mul L hmon.ne_zero hχ₁.ne_zero] at h
          omega)
      rw [this]

end Count

end Langlands.Algebra.DegreeDeterminant
