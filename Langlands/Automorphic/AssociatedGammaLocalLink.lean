import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Correspondence.AutomorphicGammaGerm

/-!
# The gamma factor of a finite pair factor choice

The gamma factor `ε(s) L∨(1 - s) / L(s)` built from the local factors of a finite pair
factor choice is the polynomial gamma expression of its chosen L-polynomials and epsilon
monomial. It has the rational continuation `rationalGammaExpression`, and this rational
function is the actual automorphic pair gamma factor when the dual presentations have the
smooth duals as local classes.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Polynomial

namespace Langlands.RankinSelberg

/-- A polynomial with nonzero constant coefficient, evaluated at `q^(-s)` with `q > 1`, is
nonzero on a right half-plane. -/
theorem eval_spectralPoint_ne_zero_of_coeff {q : ℕ} (hq : 1 < q) {P : ℂ[X]}
    (hP : P.coeff 0 ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P.eval (spectralPoint q s) ≠ 0 := by
  have h0 : P.eval 0 ≠ 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((P.continuous.continuousAt (x := 0)).eventually_ne h0)
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨-Real.logb q δ, fun s hs => hball ?_⟩
  rw [dist_zero_right, HighlyRamified.norm_spectralPoint hq0]
  calc (q : ℝ) ^ (-s.re) < (q : ℝ) ^ (Real.logb q δ) :=
        Real.rpow_lt_rpow_of_exponent_lt hqR (by linarith)
    _ = δ := Real.rpow_logb (by positivity) hqR.ne' hδ

/-- A nonzero polynomial does not vanish at `q^(-s)` on a right half-plane. -/
theorem eval_spectralPoint_ne_zero_of_ne_zero {q : ℕ} (hq : 1 < q) {P : ℂ[X]} (hP : P ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P.eval (spectralPoint q s) ≠ 0 := by
  obtain ⟨Q, hPQ, hQ⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  simp only [map_zero, sub_zero] at hPQ hQ
  have hQ0 : Q.coeff 0 ≠ 0 := fun h => hQ (Polynomial.X_dvd_iff.mpr h)
  obtain ⟨σ, hσ⟩ := eval_spectralPoint_ne_zero_of_coeff hq hQ0
  refine ⟨σ, fun s hs => ?_⟩
  rw [hPQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_ne_zero (pow_ne_zero _ (spectralPoint_ne_zero hq s)) (hσ s hs)

/-- A nonzero polynomial does not vanish at `q^(-(1-s))` on a right half-plane. -/
theorem eval_spectralPoint_one_sub_ne_zero {q : ℕ} (hq : 1 < q) {P : ℂ[X]} (hP : P ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → P.eval (spectralPoint q (1 - s)) ≠ 0 := by
  classical
  set M : ℝ := ∑ x ∈ P.roots.toFinset, ‖x‖ + 1 with hM
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ x ∈ P.roots.toFinset, ‖x‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨1 + Real.logb q M, fun s hs hroot => ?_⟩
  have hmem : P.eval (spectralPoint q (1 - s)) = 0 := hroot
  have hin : spectralPoint q (1 - s) ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact hmem
  have hle : ‖spectralPoint q (1 - s)‖ ≤ ∑ x ∈ P.roots.toFinset, ‖x‖ :=
    Finset.single_le_sum (f := fun x => ‖x‖) (fun _ _ => norm_nonneg _) hin
  rw [HighlyRamified.norm_spectralPoint hq0] at hle
  have hgt : M < (q : ℝ) ^ (-(1 - s).re) := by
    calc M = (q : ℝ) ^ (Real.logb q M) := (Real.rpow_logb (by positivity) hqR.ne' hMpos).symm
      _ < (q : ℝ) ^ (-(1 - s).re) := by
        apply Real.rpow_lt_rpow_of_exponent_lt hqR
        simp only [Complex.sub_re, Complex.one_re]
        linarith
  linarith

/-- The polynomial gamma expression has the rational continuation
`rationalGammaExpression`. -/
theorem hasRationalContinuation_polynomialGammaExpression {q : ℕ} (hq : 1 < q) {δ : ℂˣ}
    (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (c : ℂˣ) (m : ℤ) (P Pd : ℂ[X]) (hPd : Pd ≠ 0) :
    HasRationalContinuation q (polynomialGammaExpression q c m P Pd)
      (rationalGammaExpression δ c m P Pd) := by
  obtain ⟨σ₁, h₁⟩ := eval_spectralPoint_ne_zero_of_ne_zero hq
    (RatFunc.denom_ne_zero (rationalGammaExpression δ c m P Pd))
  obtain ⟨σ₂, h₂⟩ := eval_spectralPoint_one_sub_ne_zero hq hPd
  refine ⟨max σ₁ σ₂, fun s hs => ⟨h₁ s (lt_of_le_of_lt (le_max_left _ _) hs), ?_⟩⟩
  have hz := h₂ s (lt_of_le_of_lt (le_max_right _ _) hs)
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [hδ, spectralPoint_one_sub hq]
  have heval := eval_rationalGammaExpression δ c m P Pd
    (spectralPoint_ne_zero hq s) (by rwa [href])
  rw [heval, href]
  simp only [polynomialGammaExpression, epsilonMonomial, div_eq_mul_inv, inv_inv]
  ring

end Langlands.RankinSelberg

namespace Langlands.Global.CuspidalPairFunctionalEquation

namespace FinitePairFactorChoice

open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.CompletionPadic

universe u uQ

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r t : ℕ} {T Td : Automorphic.CuspidalOperatorRealization F r}
  {T' Td' : Automorphic.CuspidalOperatorRealization F t}
  {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T}
  {P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'}
  {Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td}
  {Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'}
  {h : HasIrreducibleAdmissibleComponents P} {h' : HasIrreducibleAdmissibleComponents P'}
  {hd : HasIrreducibleAdmissibleComponents Pd} {hd' : HasIrreducibleAdmissibleComponents Pd'}
  (c : FinitePairFactorChoice ψ P P' Pd Pd' h h' hd hd')

/-- The local factors of the choice at a finite place. -/
def localFactors (v : FinitePlace F) : LocalFactors :=
  ⟨c.finiteL v, c.finiteDualL v, c.finiteEpsilon v⟩

/-- The rational gamma factor of the choice at a finite place. -/
def rationalGamma (v : FinitePlace F) : RatFunc ℂ :=
  RankinSelberg.rationalGammaExpression (LocalFactor.residueReflection (padicField v))
    (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v)

/-- The gamma factor of the local factors is the polynomial gamma expression. -/
theorem localFactors_gamma (v : FinitePlace F) :
    (c.localFactors v).gamma = RankinSelberg.polynomialGammaExpression (residueCardinality v)
      (c.epsilon v).1 (c.epsilon v).2 (c.lPolynomial v) (c.dualLPolynomial v) := rfl

theorem dualLPolynomial_ne_zero (v : FinitePlace F) : c.dualLPolynomial v ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hL⟩ := c.dualLPolynomial_spec v
  exact hL.ne_zero

/-- The gamma factor of the local factors has the rational continuation
`c.rationalGamma v`. -/
theorem hasRationalContinuation_gamma (v : FinitePlace F) :
    RankinSelberg.HasRationalContinuation (residueCardinality v) (c.localFactors v).gamma
      (c.rationalGamma v) := by
  rw [localFactors_gamma]
  exact RankinSelberg.hasRationalContinuation_polynomialGammaExpression
    (one_lt_residueCardinality v) (LocalFactor.coe_residueReflection _) _ _ _ _
    (c.dualLPolynomial_ne_zero v)

/-- If the local classes of the dual presentations at `v` are the smooth duals, the
rational gamma factor of the choice is the actual automorphic pair gamma factor. -/
theorem isAutomorphicPairGammaFactor (v : FinitePlace F)
    (hdual : Correspondence.IsSmoothDual (padicField v) (localClass P h v) (localClass Pd hd v))
    (hdual' : Correspondence.IsSmoothDual (padicField v) (localClass P' h' v)
      (localClass Pd' hd' v)) :
    Correspondence.IsAutomorphicPairGammaFactor (padicField v) (c.additive v) (c.measure v)
      (localClass P h v) (localClass P' h' v) (c.rationalGamma v) :=
  ⟨_, _, _, _, _, hdual, hdual', c.lPolynomial_spec v, c.dualLPolynomial_spec v,
    c.epsilon_spec v, rfl⟩

end FinitePairFactorChoice

end Langlands.Global.CuspidalPairFunctionalEquation
