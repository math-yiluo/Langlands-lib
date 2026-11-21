import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Algebra.Ring.GeomSum

/-! # The first affected degree of the standard Lubin–Tate equation -/

noncomputable section

namespace Langlands.FormalGroup.LubinTateStandard

open MvPowerSeries
open scoped ENat

universe u

variable {A : Type u} [CommRing A] {σ : Type}

/-- Apply the standard polynomial `πT + T^q` to a formal series. -/
def standardPolynomial (π : A) (q : ℕ) (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  π • f + f ^ q

/-- The difference between applying the polynomial after a series and
substituting the polynomial in all the variables before the series. -/
def intertwinerDefect (π : A) (q : ℕ) (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  standardPolynomial π q f - f.subst (fun i => standardPolynomial π q (X i))

theorem standardPolynomial_constantCoeff (π : A) {q : ℕ} (hq : q ≠ 0)
    {f : MvPowerSeries σ A} (hf : f.constantCoeff = 0) :
    (standardPolynomial π q f).constantCoeff = 0 := by
  simp only [standardPolynomial, map_add, constantCoeff_smul, map_pow, hf, smul_zero,
    zero_pow hq, add_zero]

private theorem order_prod_of_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ A) (n : ι → ℕ)
    (h : ∀ i ∈ s, (n i : ℕ∞) ≤ (f i).order) :
    (↑(∑ i ∈ s, n i) : ℕ∞) ≤ (∏ i ∈ s, f i).order := by
  rw [Nat.cast_sum]
  exact (Finset.sum_le_sum h).trans (le_order_prod f s)

private theorem homogeneousComponent_prod_of_le {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ A) (n : ι → ℕ)
    (h : ∀ i ∈ s, (n i : ℕ∞) ≤ (f i).order) :
    homogeneousComponent (∑ i ∈ s, n i) (∏ i ∈ s, f i) =
      ∏ i ∈ s, homogeneousComponent (n i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    ext d
    by_cases hd : d = 0 <;> simp [coeff_homogeneousComponent, Finsupp.degree_eq_zero_iff, coeff_one, hd]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, (n j : ℕ∞) ≤ (f j).order :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
      homogeneousComponent_mul_of_le_order (h i (Finset.mem_insert_self i s)) (order_prod_of_le s f n hs), ih hs]

private theorem homogeneousComponent_pow_of_one_le (f : MvPowerSeries σ A) (hf : 1 ≤ f.order) (n : ℕ) :
    homogeneousComponent n (f ^ n) = (homogeneousComponent 1 f) ^ n := by
  simpa using homogeneousComponent_prod_of_le (Finset.range n) (fun _ => f) (fun _ => 1) (fun _ _ => hf)

private theorem order_monomial_substitution (a : σ → MvPowerSeries σ A)
    (ha : ∀ i, (a i).constantCoeff = 0) (d : σ →₀ ℕ) :
    (d.degree : ℕ∞) ≤ (d.prod fun i n => a i ^ n).order :=
  order_prod_of_le d.support (fun i => a i ^ d i) d
    (fun i _ => le_order_pow_of_constantCoeff_eq_zero (d i) (ha i))

private theorem homogeneousComponent_monomial_substitution (a : σ → MvPowerSeries σ A)
    (ha : ∀ i, (a i).constantCoeff = 0) (d : σ →₀ ℕ) :
    homogeneousComponent d.degree (d.prod fun i n => a i ^ n) =
      d.prod fun i n => (homogeneousComponent 1 (a i)) ^ n := by
  change homogeneousComponent (∑ i ∈ d.support, d i) (∏ i ∈ d.support, a i ^ d i) = _
  rw [homogeneousComponent_prod_of_le d.support _ d
    (fun i _ => le_order_pow_of_constantCoeff_eq_zero (d i) (ha i))]
  simp only [Finsupp.prod, homogeneousComponent_pow_of_one_le _ (one_le_order_iff_constCoeff_eq_zero.mpr (ha _))]

variable [Finite σ]

private theorem coeff_subst_eq_of_order {f : MvPowerSeries σ A} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order)
    {a b : σ → MvPowerSeries σ A} (ha : ∀ i, (a i).constantCoeff = 0)
    (hb : ∀ i, (b i).constantCoeff = 0)
    (hab : ∀ i, homogeneousComponent 1 (a i) = homogeneousComponent 1 (b i))
    (d : σ →₀ ℕ) (hd : d.degree ≤ n) : coeff d (f.subst a) = coeff d (f.subst b) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha), coeff_subst (hasSubst_of_constantCoeff_zero hb)]
  apply finsum_congr
  intro e
  by_cases he : coeff e f = 0
  · simp [he]
  have hn : n ≤ e.degree := by exact_mod_cast hf.trans (order_le he)
  have hde : d.degree ≤ e.degree := hd.trans hn
  by_cases h : d.degree = e.degree
  · have hcomp : homogeneousComponent e.degree (e.prod fun i k => a i ^ k) =
        homogeneousComponent e.degree (e.prod fun i k => b i ^ k) := by
      rw [homogeneousComponent_monomial_substitution a ha, homogeneousComponent_monomial_substitution b hb]
      simp only [hab]
    have hc := congrArg (coeff d) hcomp
    simp only [coeff_homogeneousComponent, h, ite_true] at hc
    rw [hc]
  · have hlt : (d.degree : ℕ∞) < (e.degree : ℕ∞) := by exact_mod_cast lt_of_le_of_ne hde h
    rw [coeff_of_lt_order (hlt.trans_le (order_monomial_substitution a ha e)),
      coeff_of_lt_order (hlt.trans_le (order_monomial_substitution b hb e))]

omit [Finite σ] in
private theorem coeff_pow_sub_pow {f g : MvPowerSeries σ A} (hf : f.constantCoeff = 0)
    (hg : g.constantCoeff = 0) {n q : ℕ} (hq : 2 ≤ q) (hfg : (n : ℕ∞) ≤ (f - g).order)
    (d : σ →₀ ℕ) (hd : d.degree ≤ n) : coeff d (f ^ q - g ^ q) = 0 := by
  let S := ∑ i ∈ Finset.range q, f ^ i * g ^ (q - 1 - i)
  have hS : 1 ≤ (S : MvPowerSeries σ A).order := by
    apply one_le_order_iff_constCoeff_eq_zero.mpr
    dsimp [S]
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp only [map_mul, map_pow, hf, hg]
    by_cases hi : i = 0
    · have he : q - 1 - i ≠ 0 := by omega
      rw [zero_pow he, mul_zero]
    · rw [zero_pow hi, zero_mul]
  have hpow : f ^ q - g ^ q = (f - g) * S := ((Commute.all f g).mul_geom_sum₂ q).symm
  rw [hpow]
  apply coeff_of_lt_order
  have hstep : (d.degree : ℕ∞) < (n : ℕ∞) + 1 := by
    exact_mod_cast Nat.lt_succ_of_le hd
  exact hstep.trans_le ((add_le_add hfg hS).trans le_order_mul)

/-- In the first possibly affected degree, changing the input changes the
intertwining defect by the coefficient times `π − π^degree`. -/
theorem coeff_intertwinerDefect_sub (π : A) {q n : ℕ} (hq : 2 ≤ q) {f g : MvPowerSeries σ A}
    (hf : f.constantCoeff = 0) (hg : g.constantCoeff = 0) (hfg : (n : ℕ∞) ≤ (f - g).order)
    (d : σ →₀ ℕ) (hd : d.degree ≤ n) :
    coeff d (intertwinerDefect π q f - intertwinerDefect π q g) =
      (π - π ^ d.degree) * coeff d (f - g) := by
  let a : σ → MvPowerSeries σ A := fun i => standardPolynomial π q (X i)
  let b : σ → MvPowerSeries σ A := fun i => π • X i
  have ha (i : σ) : (a i).constantCoeff = 0 :=
    standardPolynomial_constantCoeff π (by omega) (constantCoeff_X i)
  have hb (i : σ) : (b i).constantCoeff = 0 := by simp [b, constantCoeff_smul]
  have hab (i : σ) : homogeneousComponent 1 (a i) = homogeneousComponent 1 (b i) := by
    have hq' : (1 : ℕ∞) < q := by exact_mod_cast Nat.lt_of_succ_le hq
    have horder := hq'.trans_le (le_order_pow_of_constantCoeff_eq_zero q (constantCoeff_X (R := A) i))
    have hpow := homogeneousComponent_of_lt_order_eq_zero horder
    change homogeneousComponent 1 (b i + X i ^ q) = _
    rw [map_add, hpow, add_zero]
  have hc := coeff_subst_eq_of_order hfg ha hb hab d hd
  have hrescale : (f - g).subst b = rescale (fun _ => π) (f - g) :=
    (rescale_eq_subst (fun _ => π) (f - g)).symm
  rw [hrescale, coeff_rescale, Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply] at hc
  have heq : intertwinerDefect π q f - intertwinerDefect π q g =
      π • (f - g) + (f ^ q - g ^ q) - (f - g).subst a := by
    unfold intertwinerDefect standardPolynomial
    change (π • f + f ^ q - f.subst a) - (π • g + g ^ q - g.subst a) = _
    rw [subst_sub (hasSubst_of_constantCoeff_zero ha), smul_sub]
    abel
  rw [heq, map_sub, map_add, coeff_smul, coeff_pow_sub_pow hf hg hq hfg d hd, add_zero, hc, sub_mul]

end Langlands.FormalGroup.LubinTateStandard
