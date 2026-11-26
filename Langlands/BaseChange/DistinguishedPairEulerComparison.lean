import Langlands.Global.Factors.RelativeWeilAssemblyHecke
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction
import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.PairGammaOrder

/-! # Comparing distinguished Euler denominators in completed pair equations -/

noncomputable section

set_option autoImplicit false

universe u v

namespace Langlands.BaseChange

open Polynomial RankinSelberg LocalFactor.Archimedean
open Global.FunctionalEquationComparison RelativeWeilEngine
open scoped BigOperators

local notation "D(" blocks ")" => LocalFactor.ReciprocalEntire.denominator (gammaProduct blocks)
local notation "Γ(" blocks ")" => (fun z : ℂ => (D(blocks) z)⁻¹)
local notation "value(" q ", " P ")" => (fun z : ℂ => Polynomial.eval (spectralPoint q z) P)

private theorem exists_spectralPoint_im_gt {q : ℕ} (hq : 1 < q) {x : ℂ} (hx : x ≠ 0) (R : ℝ) :
    ∃ z : ℂ, spectralPoint q z = x ∧ R < z.im := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  let a := Real.log (q : ℝ)
  have ha : 0 < a := Real.log_pos hqR
  let z₀ := -(Complex.log x) / (a : ℂ)
  let period := 2 * Real.pi / a
  have hp : 0 < period := div_pos (mul_pos (by norm_num) Real.pi_pos) ha
  obtain ⟨n, hn⟩ := exists_nat_gt ((R - z₀.im) / period)
  refine ⟨z₀ + ((n * period : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · rw [spectralPoint_eq_spectralParameter q (zero_lt_one.trans hqR)]
    change Complex.exp (-(z₀ + ((n * period : ℝ) : ℂ) * Complex.I) * (a : ℂ)) = x
    have h : -(z₀ + ((n * period : ℝ) : ℂ) * Complex.I) * (a : ℂ) =
        Complex.log x - (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      simp only [z₀, period, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]
      field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
      ring
    rw [h, sub_eq_add_neg, Complex.exp_add, Complex.exp_log hx,
      Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one, mul_one]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, zero_mul, add_zero]
    linarith [(div_lt_iff₀ hp).mp hn]

private def gammaShiftIm : GammaBlock → ℝ
  | .real a | .complex a => a.im

private theorem abs_im_of_gammaPole {blocks : List GammaBlock} {z : ℂ}
    (hz : D(blocks) z = 0) : ∃ b ∈ blocks, |z.im| = |gammaShiftIm b| := by
  obtain ⟨b, hb, hp⟩ := (gammaProduct_isPole blocks z).mp hz
  refine ⟨b, hb, ?_⟩
  have him : z.im = -gammaShiftIm b := by
    cases b with
    | real a =>
      obtain ⟨n, hn⟩ := (GammaBlock.real_isPole a z).mp hp
      have h := congrArg Complex.im hn
      simp [Complex.mul_im] at h
      dsimp [gammaShiftIm]
      linarith
    | complex a =>
      obtain ⟨n, hn⟩ := (GammaBlock.complex_isPole a z).mp hp
      have h := congrArg Complex.im hn
      simp at h
      dsimp [gammaShiftIm]
      linarith
  rw [him, abs_neg]

private theorem exists_regular_spectralPoint {q : ℕ} (hq : 1 < q) {x : ℂ} (hx : x ≠ 0)
    (A B Ad Bd : List GammaBlock) : ∃ z : ℂ, spectralPoint q z = x ∧
      D(A) z ≠ 0 ∧ D(B) z ≠ 0 ∧ D(Ad) (1 - z) ≠ 0 ∧ D(Bd) (1 - z) ≠ 0 := by
  classical
  let blocks := (A ++ B) ++ (Ad ++ Bd)
  let heights := blocks.toFinset.image (fun b => |gammaShiftIm b|)
  obtain ⟨R, hR⟩ := heights.finite_toSet.bddAbove
  obtain ⟨z, hz, hzR⟩ := exists_spectralPoint_im_gt hq hx R
  have hregular (C : List GammaBlock) (hC : ∀ b ∈ C, b ∈ blocks)
      (s : ℂ) (hs : R < |s.im|) : D(C) s ≠ 0 := by
    intro he
    obtain ⟨b, hb, hbs⟩ := abs_im_of_gammaPole he
    have hmem : |gammaShiftIm b| ∈ heights := Finset.mem_image.mpr
      ⟨b, List.mem_toFinset.mpr (hC b hb), rfl⟩
    exact (not_le_of_gt (hs.trans_eq hbs)) (hR hmem)
  have hzim := hzR.trans_le (le_abs_self z.im)
  have hreflection : R < |(1 - z).im| := by simpa using hzim
  exact ⟨z, hz, hregular A (fun b hb => by simp [blocks, hb]) z hzim,
    hregular B (fun b hb => by simp [blocks, hb]) z hzim,
    hregular Ad (fun b hb => by simp [blocks, hb]) (1 - z) hreflection,
    hregular Bd (fun b hb => by simp [blocks, hb]) (1 - z) hreflection⟩

private theorem eq_of_normalized_rootMultiplicities {P Q : ℂ[X]}
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (h : ∀ x : ℂ, P.rootMultiplicity x = Q.rootMultiplicity x) : P = Q := by
  classical
  have hroots : P.roots = Q.roots := Multiset.ext.mpr fun x => by simpa only [count_roots] using h x
  have hsplitP : P.Splits := IsAlgClosed.splits P
  have hsplitQ : Q.Splits := IsAlgClosed.splits Q
  have heP := hsplitP.eval_eq_prod_roots 0
  have heQ := hsplitQ.eval_eq_prod_roots 0
  rw [← coeff_zero_eq_eval_zero, hP, hroots] at heP
  rw [← coeff_zero_eq_eval_zero, hQ] at heQ
  have hn : (Q.roots.map ((0 : ℂ) - ·)).prod ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heQ
    exact one_ne_zero heQ
  have hl := mul_right_cancel₀ hn (heP.symm.trans heQ)
  calc
    P = C P.leadingCoeff * (P.roots.map (X - C ·)).prod := hsplitP.eq_prod_roots
    _ = C Q.leadingCoeff * (Q.roots.map (X - C ·)).prod := by rw [hl, hroots]
    _ = Q := hsplitQ.eq_prod_roots.symm

private theorem eq_of_cleared_distinguishedEuler
    {q : ℕ} (hq : 1 < q) {P Pd Q Qd : ℂ[X]} (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1)
    (A Ad B Bd : List GammaBlock) (a b : ℂ → ℂ)
    (ha : ∀ z, AnalyticAt ℂ a z ∧ a z ≠ 0) (hb : ∀ z, AnalyticAt ℂ b z ∧ b z ≠ 0)
    (hPsep : ∀ x : ℂ, x ≠ 0 → P.eval x = 0 → Pd.eval ((q : ℂ)⁻¹ / x) ≠ 0)
    (hQsep : ∀ x : ℂ, x ≠ 0 → Q.eval x = 0 → Qd.eval ((q : ℂ)⁻¹ / x) ≠ 0)
    (heq : MeromorphicEq
      (fun z => (a z * D(A) z * D(Bd) (1 - z) * value(q, Qd) (1 - z)) * value(q, P) z)
      (fun z => (b z * D(B) z * D(Ad) (1 - z) * value(q, Pd) (1 - z)) * value(q, Q) z)) : P = Q := by
  have hpos := Nat.zero_lt_one.trans hq
  have hanalytic (S : ℂ[X]) (z : ℂ) : AnalyticAt ℂ (value(q, S)) z :=
    (Global.CuspidalPairBoundaryNonvanishing.differentiable_eval_spectralPoint S hpos).analyticAt z
  let left := fun z => a z * D(A) z * D(Bd) (1 - z) * value(q, Qd) (1 - z)
  let right := fun z => b z * D(B) z * D(Ad) (1 - z) * value(q, Pd) (1 - z)
  have hreflect (z : ℂ) : AnalyticAt ℂ (fun s : ℂ => 1 - s) z :=
    analyticAt_const.sub analyticAt_id
  have hl (z : ℂ) : AnalyticAt ℂ left z :=
    (((ha z).1.mul ((gammaProduct A).entire.analyticAt z)).mul
      (((gammaProduct Bd).entire.analyticAt (1 - z)).comp (hreflect z))).mul
      ((hanalytic Qd (1 - z)).comp (hreflect z))
  have hr (z : ℂ) : AnalyticAt ℂ right z :=
    (((hb z).1.mul ((gammaProduct B).entire.analyticAt z)).mul
      (((gammaProduct Ad).entire.analyticAt (1 - z)).comp (hreflect z))).mul
      ((hanalytic Pd (1 - z)).comp (hreflect z))
  have horder (S : ℂ[X]) (hS : S.coeff 0 = 1) (z : ℂ) :
      meromorphicOrderAt (value(q, S)) z = (S.rootMultiplicity (spectralPoint q z) : ℤ) :=
    meromorphicOrderAt_eval_spectralPoint q hq S (ne_zero_of_coeff_zero_eq_one hS) z
  apply eq_of_normalized_rootMultiplicities hP hQ
  intro x
  by_cases hx : x = 0
  · subst x
    have hp : P.eval 0 ≠ 0 := by rw [← coeff_zero_eq_eval_zero, hP]; exact one_ne_zero
    have hq' : Q.eval 0 ≠ 0 := by rw [← coeff_zero_eq_eval_zero, hQ]; exact one_ne_zero
    rw [rootMultiplicity_eq_zero hp, rootMultiplicity_eq_zero hq']
  obtain ⟨z, hz, hAz, hBz, hAdz, hBdz⟩ := exists_regular_spectralPoint hq hx A B Ad Bd
  have hcompare := meromorphicOrderAt_congr (heq z)
  change meromorphicOrderAt (left * value(q, P)) z =
    meromorphicOrderAt (right * value(q, Q)) z at hcompare
  apply le_antisymm
  · by_cases hroot : P.eval x = 0
    · have hright : right z ≠ 0 := mul_ne_zero
        (mul_ne_zero (mul_ne_zero (hb z).2 hBz) hAdz) (by
          change Pd.eval (spectralPoint q (1 - z)) ≠ 0
          rw [spectralPoint_one_sub hq z, hz]
          exact hPsep x hx hroot)
      rw [meromorphicOrderAt_mul (hl z).meromorphicAt (hanalytic P z).meromorphicAt,
        meromorphicOrderAt_mul_of_ne_zero (hr z) hright, horder P hP, horder Q hQ, hz] at hcompare
      have hle := le_add_of_nonneg_left (a := ((P.rootMultiplicity x : ℤ) : WithTop ℤ))
        (hl z).meromorphicOrderAt_nonneg
      rw [hcompare] at hle
      exact_mod_cast hle
    · rw [rootMultiplicity_eq_zero hroot]
      exact Nat.zero_le _
  · by_cases hroot : Q.eval x = 0
    · have hleft : left z ≠ 0 := mul_ne_zero
        (mul_ne_zero (mul_ne_zero (ha z).2 hAz) hBdz) (by
          change Qd.eval (spectralPoint q (1 - z)) ≠ 0
          rw [spectralPoint_one_sub hq z, hz]
          exact hQsep x hx hroot)
      rw [meromorphicOrderAt_mul_of_ne_zero (hl z) hleft,
        meromorphicOrderAt_mul (hr z).meromorphicAt (hanalytic Q z).meromorphicAt,
        horder P hP, horder Q hQ, hz] at hcompare
      have hle := le_add_of_nonneg_left (a := ((Q.rootMultiplicity x : ℤ) : WithTop ℤ))
        (hr z).meromorphicOrderAt_nonneg
      rw [← hcompare] at hle
      exact_mod_cast hle
    · rw [rootMultiplicity_eq_zero hroot]
      exact Nat.zero_le _

/-- Compare two normalized forward Euler denominators in completed equations.
The finite Euler products agree after multiplying out the respective forward
and dual denominators, all expressed in the same residue variable. -/
def DistinguishedPairEulerFromEquationsStatement : Prop :=
  ∀ (I : Type u) (J : Type v) (S : Finset I) (T : Finset J)
    (l ld e : I → ℂ → ℂ) (l' ld' e' : J → ℂ → ℂ)
    (A Ad B Bd : List GammaBlock) (Ae Be : ℂ → ℂ)
    (q : ℕ) (P Pd Q Qd : ℂ[X]),
    1 < q → P.coeff 0 = 1 → Q.coeff 0 = 1 →
    HasGlobalEquation l ld e Γ(A) Γ(Ad) Ae S →
    HasGlobalEquation l' ld' e' Γ(B) Γ(Bd) Be T →
    (∀ z, AnalyticAt ℂ (fun s => Ae s * ∏ v ∈ S, e v s) z ∧ Ae z * (∏ v ∈ S, e v z) ≠ 0) →
    (∀ z, AnalyticAt ℂ (fun s => Be s * ∏ w ∈ T, e' w s) z ∧ Be z * (∏ w ∈ T, e' w z) ≠ 0) →
    (∃ σ : ℝ, ∀ z : ℂ, σ < z.re → ∃ p pd r rd : ℂ,
      HasProd (fun v => l v z) p ∧ HasProd (fun w => l' w z) r ∧
      HasProd (fun v => ld v z) pd ∧ HasProd (fun w => ld' w z) rd ∧
      value(q, P) z * p = value(q, Q) z * r ∧ value(q, Pd) z * pd = value(q, Qd) z * rd) →
    (∀ x : ℂ, x ≠ 0 → P.eval x = 0 → Pd.eval ((q : ℂ)⁻¹ / x) ≠ 0) →
    (∀ x : ℂ, x ≠ 0 → Q.eval x = 0 → Qd.eval ((q : ℂ)⁻¹ / x) ≠ 0) →
    P = Q

/-- Continue the two comparisons after multiplying out the denominators, and
compare root orders in the resulting cleared equality. -/
theorem distinguishedPairEulerFromEquations : DistinguishedPairEulerFromEquationsStatement.{u, v} := by
  intro I J S T l ld e l' ld' e' A Ad B Bd Ae Be q P Pd Q Qd hq hP hQ hF hE ha hb hEuler hPsep hQsep
  obtain ⟨σF, L, Ld, hL, hLd, hpF, hFE⟩ := hF
  obtain ⟨σE, U, Ud, hU, hUd, hpE, hEE⟩ := hE
  obtain ⟨σ, hprod⟩ := hEuler
  let a (z : ℂ) := Ae z * ∏ v ∈ S, e v z
  let b (z : ℂ) := Be z * ∏ w ∈ T, e' w z
  have hmer (R : ℂ[X]) : Meromorphic (value(q, R)) := fun z =>
    ((Global.CuspidalPairBoundaryNonvanishing.differentiable_eval_spectralPoint R
      (Nat.zero_lt_one.trans hq)).analyticAt z).meromorphicAt
  have hhalf (z : ℂ) (hz : max (max σF σE) σ < z.re) :
      value(q, P) z * L z = value(q, Q) z * U z ∧
      value(q, Pd) z * Ld z = value(q, Qd) z * Ud z := by
    obtain ⟨p, pd, r, rd, hp, hr, hpd, hrd, h, hd⟩ := hprod z ((le_max_right _ _).trans_lt hz)
    obtain ⟨⟨hLz, -⟩, hLdz, -⟩ := hpF z
      (((le_max_left σF σE).trans (le_max_left _ σ)).trans_lt hz)
    obtain ⟨⟨hUz, -⟩, hUdz, -⟩ := hpE z
      (((le_max_right σF σE).trans (le_max_left _ σ)).trans_lt hz)
    simpa only [hLz.unique hp, hUz.unique hr, hLdz.unique hpd, hUdz.unique hrd] using And.intro h hd
  have hsame := eq_on_halfplane_meromorphicEq
    (fun z => (hmer P z).mul (hL z)) (fun z => (hmer Q z).mul (hU z))
    (fun z hz => (hhalf z hz).1)
  have hsameDual := (eq_on_halfplane_meromorphicEq
    (fun z => (hmer Pd z).mul (hLd z)) (fun z => (hmer Qd z).mul (hUd z))
    (fun z hz => (hhalf z hz).2)).reflect
  have hUdnz := nonzeroMeromorphic_of_ne_zero_halfPlane hUd σE (fun z hz => (hpE z hz).2.2)
  apply eq_of_cleared_distinguishedEuler hq hP hQ A Ad B Bd a b ha hb hPsep hQsep
  intro w
  filter_upwards [hFE w, hEE w, hsame w, hsameDual w, hUdnz.reflect.eventually_ne_zero w,
    (nonzeroMeromorphic_denominator (gammaProduct A)).eventually_ne_zero w,
    (nonzeroMeromorphic_denominator (gammaProduct B)).eventually_ne_zero w,
    (nonzeroMeromorphic_denominator (gammaProduct Ad)).reflect.eventually_ne_zero w,
    (nonzeroMeromorphic_denominator (gammaProduct Bd)).reflect.eventually_ne_zero w]
    with z hf he hc hd hu hA hB hAd hBd
  change L z * Γ(A) z = a z * (Ld (1 - z) * Γ(Ad) (1 - z)) at hf
  change U z * Γ(B) z = b z * (Ud (1 - z) * Γ(Bd) (1 - z)) at he
  field_simp [hA, hAd] at hf
  field_simp [hB, hBd] at he
  simp only [Pi.mul_apply] at hc hd
  apply mul_right_cancel₀ hu
  linear_combination he * (value(q, Q) z * value(q, Pd) (1 - z) * D(Ad) (1 - z)) -
    hf * (value(q, P) z * value(q, Pd) (1 - z) * D(Bd) (1 - z)) +
    hc * (D(Ad) (1 - z) * value(q, Pd) (1 - z) * D(Bd) (1 - z)) -
    hd * (a z * D(A) z * value(q, P) z * D(Bd) (1 - z))

end Langlands.BaseChange
