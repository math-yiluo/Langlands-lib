import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.GroupTheory.Sylow
import Mathlib.Analysis.Real.Sqrt

/-!
# Irreducible polynomials over a real closed subfield of `ℝ` have degree at most two

Let `R` be a real closed field (Mathlib's `IsRealClosed`) with a ring map `τ : R → ℝ`. The map
orders `R`: an element is a square exactly when its image is nonnegative. This module proves
Artin's form of the fundamental theorem of algebra: every irreducible polynomial over `R` has
degree at most `2`.

* Odd-degree extensions of `R` are trivial: a primitive element has an odd-degree irreducible
  minimal polynomial, which has a root.
* Every element of a quadratic extension of `R` is a square: the extension is `R(ι)` with
  `ι² = -1`, and `a + bι` has the square root `c + dι` with `c² = (r + a)/2`, `d² = (r - a)/2`,
  `r² = a² + b²`.
* A field all of whose elements are squares has no quadratic extension (characteristic `0`).
* In the splitting field of an irreducible `g`, a Sylow `2`-subgroup of the Galois group has
  odd-degree fixed field, so the group is a `2`-group. A subgroup chain of indices `2` and `2`
  would give a quadratic extension of a quadratic extension of `R`. Hence the splitting field
  has degree at most `2`.
-/

noncomputable section

universe u v

open Polynomial Module

namespace Langlands.FieldTheory.RealClosedDegree

section Square

variable {R : Type u} [Field R] [IsRealClosed R] (τ : R →+* ℝ)

/-- An element with nonnegative image is a square. -/
theorem isSquare_of_nonneg {x : R} (hx : 0 ≤ τ x) : IsSquare x := by
  rcases IsRealClosed.isSquare_or_isSquare_neg x with h | ⟨t, ht⟩
  · exact h
  · have h1 := congrArg τ ht
    rw [map_neg, map_mul] at h1
    have h2 : τ x = 0 := by nlinarith [mul_self_nonneg (τ t)]
    rw [(map_eq_zero τ).mp h2]
    exact ⟨0, by rw [mul_zero]⟩

/-- A square root with nonnegative image. -/
theorem exists_sq_eq_of_nonneg {x : R} (hx : 0 ≤ τ x) : ∃ r : R, r * r = x ∧ 0 ≤ τ r := by
  obtain ⟨r, hr⟩ := isSquare_of_nonneg τ hx
  rcases le_total 0 (τ r) with h | h
  · exact ⟨r, hr.symm, h⟩
  · exact ⟨-r, by rw [neg_mul_neg, hr], by rw [map_neg]; linarith⟩

end Square

section Odd

variable {R : Type u} [Field R] [IsRealClosed R]

/-- **Odd-degree extensions of a real closed field are trivial.** -/
theorem finrank_eq_one_of_odd {L : Type v} [Field L] [Algebra R L] [FiniteDimensional R L]
    (h : Odd (finrank R L)) : finrank R L = 1 := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element R L
  have hint : IsIntegral R α := .of_finite R α
  have hdeg : (minpoly R α).natDegree = finrank R L := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree (hdeg ▸ h)
  have h1 := degree_eq_one_of_irreducible_of_root (minpoly.irreducible hint) hr
  rw [← hdeg, natDegree_eq_of_degree_eq_some h1]
  rfl

end Odd

section Quadratic

variable {E : Type u} {L : Type v} [Field E] [Field L] [Algebra E L]

/-- In an extension of degree `2`, an element outside the base satisfies a monic quadratic. -/
theorem exists_quadratic (hL : finrank E L = 2) :
    ∃ α : L, α ∉ Set.range (algebraMap E L) ∧ ∃ b c : E,
      α * α + algebraMap E L b * α + algebraMap E L c = 0 := by
  have : FiniteDimensional E L := Module.finite_of_finrank_eq_succ hL
  obtain ⟨α, hα⟩ : ∃ α : L, α ∉ Set.range (algebraMap E L) := by
    by_contra h
    push Not at h
    have htop : (⊥ : Subalgebra E L) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Algebra.mem_bot.mpr (h x)
    rw [Subalgebra.bot_eq_top_iff_finrank_eq_one] at htop
    omega
  refine ⟨α, hα, ?_⟩
  have hint : IsIntegral E α := .of_finite E α
  set m := minpoly E α with hm
  have hle : m.natDegree ≤ 2 := hL ▸ minpoly.natDegree_le α
  have hne1 : m.natDegree ≠ 1 := fun h1 => hα (minpoly.natDegree_eq_one_iff.mp h1)
  have hpos : 0 < m.natDegree := minpoly.natDegree_pos hint
  have h2 : m.natDegree = 2 := by omega
  refine ⟨m.coeff 1, m.coeff 0, ?_⟩
  have hev : aeval α m = 0 := minpoly.aeval E α
  rw [aeval_eq_sum_range, h2, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one] at hev
  have hc2 : m.coeff 2 = 1 := by
    rw [← h2]
    exact (minpoly.monic hint).coeff_natDegree
  rw [hc2, one_smul, pow_zero, pow_one, Algebra.smul_def, Algebra.smul_def, mul_one] at hev
  linear_combination hev

/-- **A field all of whose elements are squares has no extension of degree `2`** (when `2 ≠ 0`). -/
theorem false_of_forall_isSquare (h2 : (2 : E) ≠ 0) (hsq : ∀ z : E, IsSquare z)
    (hL : finrank E L = 2) : False := by
  obtain ⟨α, hα, b, c, hbc⟩ := exists_quadratic hL
  obtain ⟨w, hw⟩ := hsq (b * b - 4 * c)
  set γ := 2 * α + algebraMap E L b with hγ
  have hγw : (γ - algebraMap E L w) * (γ + algebraMap E L w) = 0 := by
    have hw' : algebraMap E L w * algebraMap E L w =
        algebraMap E L b * algebraMap E L b - 4 * algebraMap E L c := by
      rw [← map_mul, ← hw]
      simp [map_sub, map_mul, map_ofNat]
    rw [hγ]
    linear_combination 4 * hbc - hw'
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap E L) 2]
    exact (_root_.map_ne_zero _).mpr h2
  apply hα
  rcases mul_eq_zero.mp hγw with h | h
  · refine ⟨(w - b) / 2, ?_⟩
    rw [map_div₀, map_sub, map_ofNat, div_eq_iff h2L]
    linear_combination hγ - h
  · refine ⟨(-w - b) / 2, ?_⟩
    rw [map_div₀, map_sub, map_neg, map_ofNat, div_eq_iff h2L]
    linear_combination hγ - h

end Quadratic

section QuadraticOfRealClosed

variable {R : Type u} [Field R] [IsRealClosed R] (τ : R →+* ℝ)
variable {F : Type v} [Field F] [Algebra R F]

/-- A quadratic extension of `R` contains a square root of `-1`. -/
theorem exists_sq_eq_neg_one (hF : finrank R F = 2) :
    ∃ ι : F, ι * ι = -1 := by
  obtain ⟨α, hα, b, c, hbc⟩ := exists_quadratic hF
  set δ := b * b - 4 * c with hδ
  set γ := 2 * α + algebraMap R F b with hγ
  have hγδ : γ * γ = algebraMap R F δ := by
    rw [hγ, hδ]
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination 4 * hbc
  have h2F : (2 : F) ≠ 0 := by
    rw [← map_ofNat (algebraMap R F) 2]
    exact (_root_.map_ne_zero _).mpr two_ne_zero
  -- `δ` is not a square in `R`
  have hnsq : ¬ IsSquare δ := by
    rintro ⟨t, ht⟩
    have : (γ - algebraMap R F t) * (γ + algebraMap R F t) = 0 := by
      rw [show (γ - algebraMap R F t) * (γ + algebraMap R F t) = γ * γ -
        algebraMap R F (t * t) by rw [map_mul]; ring, hγδ, ← ht, sub_self]
    apply hα
    rcases mul_eq_zero.mp this with h | h
    · refine ⟨(t - b) / 2, ?_⟩
      rw [map_div₀, map_sub, map_ofNat, div_eq_iff h2F]
      linear_combination hγ - h
    · refine ⟨(-t - b) / 2, ?_⟩
      rw [map_div₀, map_sub, map_neg, map_ofNat, div_eq_iff h2F]
      linear_combination hγ - h
  obtain ⟨e, he⟩ := (IsRealClosed.isSquare_or_isSquare_neg δ).resolve_left hnsq
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hnsq
    rw [mul_zero, neg_eq_zero] at he
    exact ⟨0, by rw [he, mul_zero]⟩
  have he0F : algebraMap R F e ≠ 0 := (_root_.map_ne_zero _).mpr he0
  refine ⟨γ / algebraMap R F e, ?_⟩
  have : algebraMap R F e * algebraMap R F e = -algebraMap R F δ := by
    rw [← map_mul, ← he, map_neg]
  field_simp
  linear_combination hγδ + this

include τ in
/-- **Every element of a quadratic extension of `R` is a square.** -/
theorem forall_isSquare_of_finrank_eq_two (hF : finrank R F = 2) (z : F) : IsSquare z := by
  obtain ⟨ι, hι⟩ := exists_sq_eq_neg_one hF
  have : FiniteDimensional R F := Module.finite_of_finrank_eq_succ hF
  -- `1, ι` is a basis
  have hι' : ι ∉ Set.range (algebraMap R F) := by
    rintro ⟨t, rfl⟩
    rw [← map_mul, ← map_one (algebraMap R F), ← map_neg,
      (algebraMap R F).injective.eq_iff] at hι
    have := congrArg τ hι
    rw [map_mul, map_neg, map_one] at this
    nlinarith [mul_self_nonneg (τ t)]
  have hli : LinearIndependent R ![(1 : F), ι] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one, map_eq_zero] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hι'
      refine ⟨-s / t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htF : algebraMap R F t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      rw [map_div₀, map_neg, div_eq_iff htF]
      linear_combination -hst
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hF])
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two] at hz
  simp only [B, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
    Matrix.cons_val_one, Algebra.smul_def, mul_one] at hz
  set a := B.repr z 0
  set b := B.repr z 1
  -- a square root of `a + b ι`
  obtain ⟨r, hr, hr0⟩ := exists_sq_eq_of_nonneg τ
    (show 0 ≤ τ (a * a + b * b) by
      rw [map_add, map_mul, map_mul]
      exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  have hra : |τ a| ≤ τ r := by
    have h := congrArg τ hr
    rw [map_mul, map_add, map_mul, map_mul] at h
    exact abs_le.mpr ⟨by nlinarith [mul_self_nonneg (τ b)], by nlinarith [mul_self_nonneg (τ b)]⟩
  obtain ⟨c, hc, -⟩ := exists_sq_eq_of_nonneg τ
    (show 0 ≤ τ ((r + a) / 2) by
      rw [map_div₀, map_add, map_ofNat]
      apply div_nonneg _ (by norm_num)
      linarith [neg_abs_le (τ a)])
  obtain ⟨d₀, hd₀, -⟩ := exists_sq_eq_of_nonneg τ
    (show 0 ≤ τ ((r - a) / 2) by
      rw [map_div₀, map_sub, map_ofNat]
      apply div_nonneg _ (by norm_num)
      linarith [le_abs_self (τ a)])
  have hcd : (2 * c * d₀) * (2 * c * d₀) = b * b := by
    have : (2 * c * d₀) * (2 * c * d₀) = 4 * (c * c) * (d₀ * d₀) := by ring
    rw [this, hc, hd₀]
    field_simp
    linear_combination 4 * hr
  obtain ⟨d, hd, hcdb⟩ : ∃ d : R, d * d = (r - a) / 2 ∧ 2 * c * d = b := by
    have : (2 * c * d₀ - b) * (2 * c * d₀ + b) = 0 := by linear_combination hcd
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨d₀, hd₀, by linear_combination h⟩
    · exact ⟨-d₀, by rw [neg_mul_neg, hd₀], by linear_combination -h⟩
  refine ⟨algebraMap R F c + algebraMap R F d * ι, ?_⟩
  rw [← hz]
  have hcdF : algebraMap R F c * algebraMap R F c - algebraMap R F d * algebraMap R F d =
      algebraMap R F a := by
    rw [← map_mul, ← map_mul, ← map_sub, hc, hd]
    congr 1
    ring
  have hbF : 2 * algebraMap R F c * algebraMap R F d = algebraMap R F b := by
    rw [← hcdb, map_mul, map_mul, map_ofNat]
  linear_combination -hcdF - hbF * ι - (algebraMap R F d * algebraMap R F d) * hι

end QuadraticOfRealClosed

section Main

variable {R : Type u} [Field R] [IsRealClosed R] (τ : R →+* ℝ)

include τ in
/-- **Irreducible polynomials over `R` have degree at most `2`.** -/
theorem natDegree_le_two_of_irreducible {g : R[X]} (hg : Irreducible g) : g.natDegree ≤ 2 := by
  classical
  let SF := g.SplittingField
  have hsep : g.Separable := hg.separable
  have : IsGalois R SF := IsGalois.of_separable_splitting_field hsep
  have hcardG : Nat.card Gal(SF/R) = finrank R SF := IsGalois.card_aut_eq_finrank R SF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the Galois group is a `2`-group
  obtain ⟨k, hk⟩ : ∃ k, finrank R SF = 2 ^ k := by
    let P : Sylow 2 Gal(SF/R) := default
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    let F := IntermediateField.fixedField (P : Subgroup Gal(SF/R))
    have h1 : finrank F SF = Nat.card P := IntermediateField.finrank_fixedField_eq_card _
    have h2 : finrank R F * finrank F SF = finrank R SF := Module.finrank_mul_finrank R F SF
    have hidx := (P : Subgroup Gal(SF/R)).card_mul_index
    have hPpos : 0 < Nat.card P := Nat.card_pos
    have hFidx : finrank R F = (P : Subgroup Gal(SF/R)).index := by
      have : finrank R F * Nat.card P = (P : Subgroup Gal(SF/R)).index * Nat.card P := by
        rw [← h1, h2, ← hcardG, ← hidx, mul_comm, h1]
      exact Nat.eq_of_mul_eq_mul_right hPpos this
    have hodd : Odd (finrank R F) := by
      rw [hFidx, Nat.odd_iff]
      have := P.not_dvd_index
      omega
    have hF1 := finrank_eq_one_of_odd hodd
    exact ⟨n, by rw [← h2, hF1, one_mul, h1, hn]⟩
  -- the degree is at most `2`
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    obtain ⟨H', hH'⟩ := Sylow.exists_subgroup_card_pow_prime 2
      (show 2 ^ (k - 2) ∣ Nat.card Gal(SF/R) by
        rw [hcardG, hk]
        exact pow_dvd_pow 2 (Nat.sub_le k 2))
    obtain ⟨H, hH, hle⟩ := Sylow.exists_subgroup_card_pow_succ
      (show 2 ^ (k - 2 + 1) ∣ Nat.card Gal(SF/R) by
        rw [hcardG, hk]
        exact pow_dvd_pow 2 (by omega)) hH'
    let F := IntermediateField.fixedField H
    let F' := IntermediateField.fixedField H'
    have hFF' : F ≤ F' := IntermediateField.fixedField_le hle
    have hF : finrank R F = 2 := by
      have h1 : finrank F SF = 2 ^ (k - 2 + 1) := by
        rw [IntermediateField.finrank_fixedField_eq_card, hH]
      have h2 : finrank R F * finrank F SF = finrank R SF := Module.finrank_mul_finrank R F SF
      rw [h1, hk, show k = (k - 2 + 1) + 1 by omega, pow_succ, mul_comm] at h2
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
    let E := IntermediateField.extendScalars hFF'
    have hE : finrank F E = 2 := by
      have h1 : finrank F SF = 2 ^ (k - 2 + 1) := by
        rw [IntermediateField.finrank_fixedField_eq_card, hH]
      have h1' : finrank E SF = 2 ^ (k - 2) := by
        change finrank F' SF = _
        rw [IntermediateField.finrank_fixedField_eq_card, hH']
      have h2 : finrank F E * finrank E SF = finrank F SF := Module.finrank_mul_finrank F E SF
      rw [h1, h1', pow_succ, mul_comm] at h2
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
    exact false_of_forall_isSquare (E := F) (L := E) two_ne_zero
      (forall_isSquare_of_finrank_eq_two τ hF) hE
  -- a root of `g` in the splitting field
  have hdeg0 : (g.map (algebraMap R SF)).degree ≠ 0 := by
    rw [degree_map]
    exact (degree_pos_of_irreducible hg).ne'
  obtain ⟨θ, hθ⟩ := (SplittingField.splits g).exists_eval_eq_zero hdeg0
  have hθ' : aeval θ g = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have heq := minpoly.eq_of_irreducible hg hθ'
  have hle := minpoly.natDegree_le (A := R) θ
  rw [← heq, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hg.ne_zero)), hk] at hle
  calc g.natDegree ≤ 2 ^ k := hle
    _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

end Main

end Langlands.FieldTheory.RealClosedDegree
