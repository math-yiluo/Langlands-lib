import Langlands.LocalFactor.Archimedean.Definitions
import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Global.Factors.RelativeWeilAssemblyHecke
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingReduction
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Vanishing of separated distinguished Euler denominators -/

noncomputable section

set_option autoImplicit false

namespace Langlands.BaseChange

open LocalFactor.Archimedean Polynomial RankinSelberg Filter Topology
open Global.FunctionalEquationComparison RelativeWeilEngine
open Global.CuspidalPairBoundaryNonvanishing
open scoped BigOperators

private theorem exists_spectralPoint_im_gt {q : ℕ} (hq : 1 < q) {x : ℂ} (hx : x ≠ 0) (R : ℝ) :
    ∃ z : ℂ, spectralPoint q z = x ∧ R < z.im := by
  let a := Real.log (q : ℝ)
  have ha : 0 < a := Real.log_pos (by exact_mod_cast hq)
  let k := 2 * Real.pi / a
  have hk : 0 < k := div_pos (mul_pos (by norm_num) Real.pi_pos) ha
  let z₀ := -Complex.log x / (a : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt ((R - z₀.im) / k)
  have hn' := (div_lt_iff₀ hk).mp hn
  let z := z₀ + ((n * k : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans hq).ne'
    rw [spectralPoint, Complex.cpow_def_of_ne_zero hqC, ← Complex.natCast_log]
    change Complex.exp ((a : ℂ) * -z) = x
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have h : (a : ℂ) * -z = Complex.log x - (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      simp only [z, z₀, k, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
        Complex.ofReal_natCast]
      field_simp
      ring
    rw [h, sub_eq_add_neg, Complex.exp_add, Complex.exp_log hx,
      Complex.exp_neg, Complex.exp_nat_mul_two_pi_mul_I, inv_one, mul_one]
  · change R < (z₀ + ((n * k : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, zero_mul, add_zero]
    linarith

private def shiftImaginaryPart : GammaBlock → ℝ
  | .real a | .complex a => a.im

private def imaginaryBound : List GammaBlock → ℝ
  | [] => 0
  | b :: bs => max |shiftImaginaryPart b| (imaginaryBound bs)

private theorem abs_shiftImaginaryPart_le_bound {b : GammaBlock} {A : List GammaBlock} (hb : b ∈ A) :
    |shiftImaginaryPart b| ≤ imaginaryBound A := by
  induction A with
  | nil => simp at hb
  | cons a A ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_max_left _ _
    · exact (ih hb).trans (le_max_right _ _)

private theorem gammaProduct_denominator_ne_zero_of_bound (A : List GammaBlock)
    (z : ℂ) (hz : imaginaryBound A < |z.im|) : (gammaProduct A).denominator z ≠ 0 := by
  intro he
  have h : (gammaProduct A).IsPole z := he
  obtain ⟨b, hb, hp⟩ := (gammaProduct_isPole A z).mp h
  have e : z.im = -shiftImaginaryPart b := by
    cases b with
    | real a =>
      obtain ⟨n, hn⟩ := (GammaBlock.real_isPole a z).mp hp
      have hi := congrArg Complex.im hn
      simp [Complex.mul_im] at hi
      dsimp [shiftImaginaryPart]
      linarith
    | complex a =>
      obtain ⟨n, hn⟩ := (GammaBlock.complex_isPole a z).mp hp
      have hi := congrArg Complex.im hn
      simp at hi
      dsimp [shiftImaginaryPart]
      linarith
  have hbnd := abs_shiftImaginaryPart_le_bound hb
  rw [e, abs_neg] at hz
  exact (not_lt_of_ge hbnd) hz

private theorem exists_regular_spectralPoint {q : ℕ} (hq : 1 < q) {x : ℂ} (hx : x ≠ 0)
    (A Ad : List GammaBlock) :
    ∃ z : ℂ, spectralPoint q z = x ∧ (gammaProduct A).denominator z ≠ 0 ∧
      (gammaProduct Ad).denominator (1 - z) ≠ 0 := by
  obtain ⟨z, hz, him⟩ := exists_spectralPoint_im_gt hq hx (max (imaginaryBound A) (imaginaryBound Ad))
  refine ⟨z, hz, gammaProduct_denominator_ne_zero_of_bound A z
    ((lt_of_le_of_lt (le_max_left _ _) him).trans_le (le_abs_self _)), ?_⟩
  apply gammaProduct_denominator_ne_zero_of_bound Ad
  simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
    ((lt_of_le_of_lt (le_max_right _ _) him).trans_le (le_abs_self z.im))

private theorem polynomial_eq_one_of_forall_eval_ne_zero (P : ℂ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ x, P.eval x ≠ 0) : P = 1 := by
  have hdeg : P.natDegree = 0 := by
    by_contra hn
    have hd : P.degree ≠ 0 := fun h => hn (natDegree_eq_of_degree_eq_some h)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root P hd
    exact hP x hx
  rw [eq_C_of_natDegree_eq_zero hdeg, h0, C_1]

/-- For normalized polynomials at an actual residue base, a cleared completed equation
and separation from reflected dual roots force both polynomials to be one. -/
def DistinguishedEulerPolynomialVanishingStatement : Prop :=
  ∀ (q : ℕ), 1 < q →
    ∀ (P Pd : ℂ[X]) (A Ad B Bd : List GammaBlock) (e e' : ℂ → ℂ),
      P.coeff 0 = 1 → Pd.coeff 0 = 1 → (∀ z, e z ≠ 0) → (∀ z, e' z ≠ 0) →
      (∀ x : ℂ, x ≠ 0 → P.eval x = 0 → Pd.eval ((q : ℂ)⁻¹ / x) ≠ 0) →
      (∀ z : ℂ,
        e z * (gammaProduct A).denominator z * (gammaProduct Bd).denominator (1 - z) *
            Pd.eval (spectralPoint q (1 - z)) =
          e' z * (gammaProduct B).denominator z * (gammaProduct Ad).denominator (1 - z) *
            P.eval (spectralPoint q z)) →
      P = 1 ∧ Pd = 1

/-- Each nonzero spectral fiber has points beyond all the imaginary parts of the
Gamma poles. Evaluate the cleared equation at such a point over a putative root. -/
theorem distinguishedEulerPolynomialVanishing : DistinguishedEulerPolynomialVanishingStatement := by
  intro q hq P Pd A Ad B Bd e e' h0 hd0 he he' hsep hEq
  have hP : P = 1 := by
    apply polynomial_eq_one_of_forall_eval_ne_zero P h0
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hz
      rw [hz, ← coeff_zero_eq_eval_zero, h0] at hx
      exact one_ne_zero hx
    obtain ⟨z, hz, ha, hbd⟩ := exists_regular_spectralPoint hq hx0 A Bd
    have hpd := hsep x hx0 hx
    have h := hEq z
    rw [spectralPoint_one_sub hq z, hz, hx, mul_zero] at h
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (he z) ha) hbd) hpd h
  refine ⟨hP, polynomial_eq_one_of_forall_eval_ne_zero Pd hd0 fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, ← coeff_zero_eq_eval_zero, hd0] at hx
    exact one_ne_zero hx
  obtain ⟨z, hz, had, hb⟩ := exists_regular_spectralPoint hq hx0 Ad B
  have h := hEq (1 - z)
  rw [sub_sub_cancel, hz, hx, mul_zero, hP, eval_one, mul_one] at h
  exact mul_ne_zero (mul_ne_zero (he' (1 - z)) hb) had h.symm

universe u v

local notation "D(" blocks ")" => LocalFactor.ReciprocalEntire.denominator (gammaProduct blocks)
local notation "Γ(" blocks ")" => fun s : ℂ => (D(blocks) s)⁻¹

/-- Extract the distinguished polynomials from completed equations whose finite Euler
products differ precisely by the reciprocals of those two polynomials. -/
def DistinguishedEulerFromEquationsStatement : Prop :=
  ∀ (Q : Type u) (R : Type v) (S : Finset Q) (T : Finset R)
    (l ld e : Q → ℂ → ℂ) (l' ld' e' : R → ℂ → ℂ)
    (A Ad B Bd : List GammaBlock) (Ae Be : ℂ → ℂ) (q : ℕ) (P Pd : ℂ[X]),
    1 < q → P.coeff 0 = 1 → Pd.coeff 0 = 1 →
    HasGlobalEquation l ld e Γ(A) Γ(Ad) Ae S →
    HasGlobalEquation l' ld' e' Γ(B) Γ(Bd) Be T →
    Continuous (fun z => Ae z * ∏ v ∈ S, e v z) →
    Continuous (fun z => Be z * ∏ w ∈ T, e' w z) →
    (∀ z, Ae z * (∏ v ∈ S, e v z) ≠ 0) →
    (∀ z, Be z * (∏ w ∈ T, e' w z) ≠ 0) →
    (Exists fun σ : ℝ => ∀ z : ℂ, σ < z.re → ∃ p pd : ℂ,
      HasProd (fun v => l v z) (P.eval (spectralPoint q z) * p) ∧
      HasProd (fun w => l' w z) p ∧
      HasProd (fun v => ld v z) (Pd.eval (spectralPoint q z) * pd) ∧
      HasProd (fun w => ld' w z) pd) →
    (∀ x : ℂ, x ≠ 0 → P.eval x = 0 → Pd.eval ((q : ℂ)⁻¹ / x) ≠ 0) →
    P = 1 ∧ Pd = 1

set_option maxHeartbeats 1000000 in
/-- Continue the Euler-product relations meromorphically, then cross-multiply the
completed equations and cancel the common nonzero dual finite product. -/
theorem distinguishedEulerFromEquations : DistinguishedEulerFromEquationsStatement.{u, v} := by
  intro Q R S T l ld e l' ld' e' A Ad B Bd Ae Be q P Pd hq hP hPd hEq hEq'
    hc hc' he he' hEuler hsep
  obtain ⟨σF, L, Ld, hL, hLd, hprodF, hFE⟩ := hEq
  obtain ⟨σE, U, Ud, hU, hUd, hprodE, hFE'⟩ := hEq'
  obtain ⟨σ, hproducts⟩ := hEuler
  let σ₀ := max (max σF σE) σ
  let f (z : ℂ) := P.eval (spectralPoint q z)
  let d (z : ℂ) := Pd.eval (spectralPoint q z)
  let a (z : ℂ) := Ae z * ∏ v ∈ S, e v z
  let b (z : ℂ) := Be z * ∏ w ∈ T, e' w z
  have hpos : 0 < q := Nat.zero_lt_one.trans hq
  have hf : Differentiable ℂ f := differentiable_eval_spectralPoint P hpos
  have hd : Differentiable ℂ d := differentiable_eval_spectralPoint Pd hpos
  have hhalf (z : ℂ) (hz : σ₀ < z.re) :
      L z = f z * U z ∧ Ld z = d z * Ud z := by
    obtain ⟨p, pd, hp, hp', hpd, hpd'⟩ := hproducts z ((le_max_right _ _).trans_lt hz)
    have hzF := ((le_max_left σF σE).trans (le_max_left _ σ)).trans_lt hz
    have hzE := ((le_max_right σF σE).trans (le_max_left _ σ)).trans_lt hz
    obtain ⟨⟨lF, -⟩, ldF, -⟩ := hprodF z hzF
    obtain ⟨⟨lE, -⟩, ldE, -⟩ := hprodE z hzE
    rw [lE.unique hp', ldE.unique hpd']
    exact ⟨lF.unique hp, ldF.unique hpd⟩
  have hsameF : MeromorphicEq L (fun z => f z * U z) :=
    eq_on_halfplane_meromorphicEq hL (fun z => (hf.analyticAt z).meromorphicAt.mul (hU z))
      (fun z hz => (hhalf z hz).1)
  have hsameD : MeromorphicEq (fun z => Ld (1 - z)) (fun z => d (1 - z) * Ud (1 - z)) :=
    (eq_on_halfplane_meromorphicEq hLd (fun z => (hd.analyticAt z).meromorphicAt.mul (hUd z))
      (fun z hz => (hhalf z hz).2)).reflect
  have hUnz := nonzeroMeromorphic_of_ne_zero_halfPlane hUd σE (fun z hz => (hprodE z hz).2.2)
  have hcross : MeromorphicEq
      (fun z => a z * D(A) z * D(Bd) (1 - z) * d (1 - z))
      (fun z => b z * D(B) z * D(Ad) (1 - z) * f z) := by
    intro w
    filter_upwards [hFE w, hFE' w, hsameF w, hsameD w, hUnz.reflect.eventually_ne_zero w,
      (nonzeroMeromorphic_denominator (gammaProduct A)).eventually_ne_zero w,
      (nonzeroMeromorphic_denominator (gammaProduct B)).eventually_ne_zero w,
      (nonzeroMeromorphic_denominator (gammaProduct Ad)).reflect.eventually_ne_zero w,
      (nonzeroMeromorphic_denominator (gammaProduct Bd)).reflect.eventually_ne_zero w]
      with z hF hE hF' hD hU₀ hA hB hAd hBd
    change L z * (D(A) z)⁻¹ = a z * (Ld (1 - z) * (D(Ad) (1 - z))⁻¹) at hF
    change U z * (D(B) z)⁻¹ = b z * (Ud (1 - z) * (D(Bd) (1 - z))⁻¹) at hE
    rw [hF', hD] at hF
    field_simp [hA, hAd] at hF
    field_simp [hB, hBd] at hE
    apply mul_right_cancel₀ hU₀
    linear_combination hE * (f z * D(Ad) (1 - z)) - hF * D(Bd) (1 - z)
  have hcont {C Cd : List GammaBlock} {m n : ℂ → ℂ} (hm : Continuous m)
      (hn : Continuous n) :
      Continuous (fun z => m z * D(C) z * D(Cd) (1 - z) * n z) :=
    ((hm.mul (gammaProduct C).entire.continuous).mul
      ((gammaProduct Cd).entire.continuous.comp (continuous_const.sub continuous_id))).mul hn
  have hdReflect : Continuous (fun z : ℂ => d (1 - z)) :=
    hd.continuous.comp (continuous_const.sub continuous_id)
  have hleft := hcont (C := A) (Cd := Bd) hc hdReflect
  have hright := hcont (C := B) (Cd := Ad) hc' hf.continuous
  apply distinguishedEulerPolynomialVanishing q hq P Pd A Ad B Bd a b hP hPd he he' hsep
  intro z
  exact tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z)
    ((hleft.continuousAt (x := z)).mono_left nhdsWithin_le_nhds)
    ((hright.continuousAt (x := z)).mono_left nhdsWithin_le_nhds) (hcross z)

end Langlands.BaseChange
