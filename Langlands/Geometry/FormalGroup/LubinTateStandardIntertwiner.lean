import Langlands.Geometry.FormalGroup.LubinTateStandardDefect
import Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import Nyll.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand

/-! # Integral intertwiners for the standard Lubin–Tate polynomial -/

noncomputable section

namespace Langlands.FormalGroup.LubinTateStandard

open MvPowerSeries IsLocalRing
open LubinTate.SameUniformizer
open scoped ENat

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)]
variable {σ : Type} [Fintype σ]
variable (π : A) (hπ : maximalIdeal A = Ideal.span {π})

local notation "q" => Nat.card (ResidueField A)
local notation "r" => IsLocalRing.residue A

private theorem card_residue_two_le : 2 ≤ q := Nat.succ_le_of_lt Finite.one_lt_card

include hπ in
omit [Finite (ResidueField A)] in
/-- The chosen generator of the maximal ideal reduces to zero. -/
theorem residue_uniformizer : r π = 0 := by
  rw [residue_eq_zero_iff, hπ]
  exact Ideal.subset_span (Set.mem_singleton π)

include hπ in
private theorem map_defect_residue (f : MvPowerSeries σ A) :
    (intertwinerDefect π q f).map r = 0 := by
  let : Fintype (ResidueField A) := Fintype.ofFinite _
  have hq := card_residue_two_le (A := A)
  have hsubst := hasSubst_of_constantCoeff_zero fun i : σ =>
    standardPolynomial_constantCoeff π (show q ≠ 0 by omega) (constantCoeff_X i)
  have hmap (u : MvPowerSeries σ A) : (standardPolynomial π q u).map r = (u.map r) ^ q := by
    simp [standardPolynomial, smul_eq_C_mul, residue_uniformizer π hπ]
  rw [intertwinerDefect, map_sub, hmap, map_subst hsubst]
  simp only [hmap, map_X, sub_eq_zero]
  simpa only [Nat.card_eq_fintype_card, MvPowerSeries.expand, substAlgHom_apply] using
    (FiniteField.MvPowerSeries.expand_card (f.map r)).symm

omit [IsLocalRing A] [Finite (ResidueField A)] in
private theorem correction_factor (n : ℕ) (hn : 2 ≤ n) :
    π - π ^ n = π * (1 - π ^ (n - 1)) := by
  have he : π ^ n = π * π ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [he, mul_sub, mul_one]

include hπ in
omit [Finite (ResidueField A)] in
private theorem correction_factor_unit (n : ℕ) (hn : 2 ≤ n) : IsUnit (1 - π ^ (n - 1)) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_sub, map_one, map_pow, residue_uniformizer π hπ, zero_pow (by omega), sub_zero]
  exact one_ne_zero

include hπ in
private theorem correction_exists (f : MvPowerSeries σ A) (d : σ →₀ ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ x, -(coeff d (intertwinerDefect π q f)) = (π - π ^ n) * x := by
  have hz := congrArg (coeff d) (map_defect_residue π hπ f)
  rw [coeff_map, map_zero, residue_eq_zero_iff, hπ, Ideal.mem_span_singleton] at hz
  obtain ⟨a, ha⟩ := dvd_neg.mpr hz
  obtain ⟨b, hb⟩ := (correction_factor_unit π hπ n hn).dvd (a := a)
  exact ⟨b, by rw [ha, hb, correction_factor π n hn, mul_assoc]⟩

private def correction (f : MvPowerSeries σ A) (n : ℕ) : MvPowerSeries σ A := fun d =>
  if d.degree = n + 2 then (correction_exists π hπ f d (n + 2) (by omega)).choose else 0

private theorem coeff_correction_of_ne (f : MvPowerSeries σ A) (n : ℕ) (d : σ →₀ ℕ)
    (h : d.degree ≠ n + 2) : coeff d (correction π hπ f n) = 0 := by
  simp [coeff_apply, correction, h]

private theorem coeff_correction_mul (f : MvPowerSeries σ A) (n : ℕ) (d : σ →₀ ℕ)
    (h : d.degree = n + 2) :
    (π - π ^ d.degree) * coeff d (correction π hπ f n) = -(coeff d (intertwinerDefect π q f)) := by
  simpa only [coeff_apply, correction, h, ite_true] using
    (correction_exists π hπ f d (n + 2) (by omega)).choose_spec.symm

private def approximation (L : σ → A) : ℕ → MvPowerSeries σ A
  | 0 => linearForm L
  | n + 1 => approximation L n + correction π hπ (approximation L n) n

private theorem coeff_approximation_succ (L : σ → A) (n : ℕ) (d : σ →₀ ℕ) (hd : d.degree < n + 2) :
    coeff d (approximation π hπ L (n + 1)) = coeff d (approximation π hπ L n) := by
  rw [approximation, map_add, coeff_correction_of_ne _ _ _ _ _ (ne_of_lt hd), add_zero]

private theorem coeff_approximation_stable (L : σ → A) (d : σ →₀ ℕ) {n m : ℕ}
    (hnm : n ≤ m) (hd : d.degree < n + 2) :
    coeff d (approximation π hπ L m) = coeff d (approximation π hπ L n) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    exact (coeff_approximation_succ π hπ L m d (by omega)).trans ih

private theorem approximation_constantCoeff (L : σ → A) (n : ℕ) :
    constantCoeff (approximation π hπ L n) = 0 := by
  change coeff 0 (approximation π hπ L n) = 0
  rw [coeff_approximation_stable π hπ L 0 (Nat.zero_le n) (by simp), approximation,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_linearForm]

private theorem approximation_order_sub (L : σ → A) (n : ℕ) :
    ((n + 2 : ℕ) : ℕ∞) ≤ (approximation π hπ L (n + 1) - approximation π hπ L n).order := by
  apply nat_le_order
  intro d hd
  rw [map_sub, coeff_approximation_succ π hπ L n d hd, sub_self]

private theorem coeff_defect_linearForm (L : σ → A) (d : σ →₀ ℕ) (hd : d.degree < 2) :
    coeff d (intertwinerDefect π q (linearForm L)) = 0 := by
  have hq := card_residue_two_le (A := A)
  have hzero : intertwinerDefect π q (0 : MvPowerSeries σ A) = 0 := by
    have ha := hasSubst_of_constantCoeff_zero fun i : σ =>
      standardPolynomial_constantCoeff π (show q ≠ 0 by omega) (constantCoeff_X i)
    unfold intertwinerDefect
    rw [← substAlgHom_apply ha, map_zero, sub_zero]
    simp [standardPolynomial, show q ≠ 0 by omega]
  have hL := constantCoeff_linearForm L
  have horder : (1 : ℕ∞) ≤ (linearForm L - (0 : MvPowerSeries σ A)).order := by
    rw [sub_zero, one_le_order_iff_constCoeff_eq_zero]
    exact hL
  have h := coeff_intertwinerDefect_sub π hq hL constantCoeff_zero horder d (by omega)
  simp only [hzero, sub_zero] at h
  by_cases hd0 : d.degree = 0
  · have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
    subst d
    simp [h, coeff_zero_eq_constantCoeff_apply]
  · have hd1 : d.degree = 1 := by omega
    simp [h, hd1]

private theorem coeff_defect_approximation (L : σ → A) (n : ℕ) (d : σ →₀ ℕ)
    (hd : d.degree < n + 2) : coeff d (intertwinerDefect π q (approximation π hπ L n)) = 0 := by
  induction n generalizing d with
  | zero => exact coeff_defect_linearForm π L d hd
  | succ n ih =>
    let f := approximation π hπ L (n + 1)
    let g := approximation π hπ L n
    have hfg : f - g = correction π hπ g n := by
      change g + correction π hπ g n - g = _
      abel
    have h := coeff_intertwinerDefect_sub π (card_residue_two_le (A := A))
      (approximation_constantCoeff π hπ L (n + 1)) (approximation_constantCoeff π hπ L n)
      (approximation_order_sub π hπ L n) d (by omega)
    change coeff d (intertwinerDefect π q f - intertwinerDefect π q g) =
      (π - π ^ d.degree) * coeff d (f - g) at h
    rw [map_sub, hfg] at h
    change coeff d (intertwinerDefect π q f) = 0
    by_cases hlt : d.degree < n + 2
    · rw [coeff_correction_of_ne π hπ g n d (ne_of_lt hlt), mul_zero] at h
      exact (sub_eq_zero.mp h).trans (ih d hlt)
    · have he : d.degree = n + 2 := by omega
      rw [coeff_correction_mul π hπ g n d he] at h
      exact (sub_add_cancel _ _).symm.trans (by rw [h, neg_add_cancel])

/-- The stabilized coefficients of the integral degree corrections. -/
def intertwiner (L : σ → A) : MvPowerSeries σ A := fun d =>
  coeff d (approximation π hπ L d.degree)

private theorem coeff_intertwiner_eq_approximation (L : σ → A) (n : ℕ) (d : σ →₀ ℕ)
    (hd : d.degree < n + 2) : coeff d (intertwiner π hπ L) = coeff d (approximation π hπ L n) := by
  change coeff d (approximation π hπ L d.degree) = _
  let m := max d.degree n
  exact (coeff_approximation_stable π hπ L d (show d.degree ≤ m from le_max_left ..) (by omega)).symm.trans
    (coeff_approximation_stable π hπ L d (show n ≤ m from le_max_right ..) hd)

/-- The stabilized coefficients have the prescribed linear term. -/
theorem intertwiner_hasLinearTerm (L : σ → A) : HasLinearTerm (intertwiner π hπ L) L := by
  apply nat_le_order
  intro d hd
  rw [map_sub, coeff_intertwiner_eq_approximation π hπ L 0 d hd, approximation, sub_self]

/-- The stabilized coefficients solve the whole intertwining equation. -/
theorem intertwiner_defect_zero (L : σ → A) : intertwinerDefect π q (intertwiner π hπ L) = 0 := by
  ext d
  let f := intertwiner π hπ L
  let g := approximation π hπ L d.degree
  have ho : (d.degree : ℕ∞) ≤ (f - g).order := by
    apply nat_le_order
    intro i hi
    rw [map_sub, coeff_intertwiner_eq_approximation π hπ L d.degree i (by omega), sub_self]
  have hf := (intertwiner_hasLinearTerm π hπ L).constantCoeff_eq_zero
  have hg := approximation_constantCoeff π hπ L d.degree
  have h := coeff_intertwinerDefect_sub π (card_residue_two_le (A := A)) hf hg ho d le_rfl
  rw [map_sub, map_sub, coeff_intertwiner_eq_approximation π hπ L d.degree d (by omega),
    sub_self, mul_zero, coeff_defect_approximation π hπ L d.degree d (by omega), sub_zero] at h
  simpa only [map_zero] using h

variable [IsDomain A]

include hπ in
/-- The standard polynomial equation has at most one solution with the given linear term. -/
theorem intertwiner_unique (hπne : π ≠ 0) {L : σ → A} {f g : MvPowerSeries σ A}
    (hf : HasLinearTerm f L) (hg : HasLinearTerm g L)
    (hF : intertwinerDefect π q f = 0) (hG : intertwinerDefect π q g = 0) : f = g := by
  ext d
  suffices H : ∀ n : ℕ, ∀ e : σ →₀ ℕ, e.degree = n → coeff e f = coeff e g from H d.degree d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro e he
    by_cases hn : n < 2
    · exact (hf.coeff_eq_linearForm e (he ▸ hn)).trans (hg.coeff_eq_linearForm e (he ▸ hn)).symm
    · have ho : (n : ℕ∞) ≤ (f - g).order := by
        apply nat_le_order
        intro i hi
        rw [map_sub, ih i.degree hi i rfl, sub_self]
      have h := coeff_intertwinerDefect_sub π (card_residue_two_le (A := A))
        hf.constantCoeff_eq_zero hg.constantCoeff_eq_zero ho e he.le
      rw [hF, hG, sub_self, map_zero, map_sub, he] at h
      have hne : π - π ^ n ≠ 0 := by
        rw [correction_factor π n (by omega)]
        exact mul_ne_zero hπne (correction_factor_unit π hπ n (by omega)).ne_zero
      exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hne)

end Langlands.FormalGroup.LubinTateStandard
