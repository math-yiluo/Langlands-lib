import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryNormalizedTests
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Polynomial normalized values and finite generation -/

noncomputable section

open Polynomial MeasureTheory
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

/-- A polynomial realized by an entire normalization of one ordinary test. -/
def IsOrdinaryNormalizationPolynomial {Test : Type*} (I : Test → ℂ → ℂ) (L : ReciprocalEntire)
    (p : ℂ[X]) : Prop :=
  ∃ (i : Test) (N : OrdinaryIntegralNormalization (I i) (fun s => (L.denominator s)⁻¹)),
    ∀ s, N.value s = p.eval s

private theorem one_mem_span_of_polynomial_cover (S : Set ℂ[X])
    (hcover : ∀ s : ℂ, ∃ p ∈ S, p.eval s ≠ 0)
    (hX : ∀ p ∈ S, X * p ∈ Submodule.span ℂ S) :
    (1 : ℂ[X]) ∈ Submodule.span ℂ S := by
  let V := Submodule.span ℂ S
  have hXV (p : ℂ[X]) (hp : p ∈ V) : X * p ∈ V := by
    refine Submodule.span_induction (fun p hp => hX p hp) (by simpa only [mul_zero] using V.zero_mem)
      (fun p q _ _ hp hq => by rw [mul_add]; exact V.add_mem hp hq) (fun c p _ hp => ?_) hp
    rw [smul_eq_C_mul, mul_left_comm, ← smul_eq_C_mul]
    exact V.smul_mem _ hp
  have hpow (n : ℕ) (p : ℂ[X]) (hp : p ∈ V) : X ^ n * p ∈ V := by
    induction n with
    | zero => simpa only [pow_zero, one_mul] using hp
    | succ n ih => rw [pow_succ', mul_assoc]; exact hXV _ ih
  have hmul (p q : ℂ[X]) (hq : q ∈ V) : p * q ∈ V := by
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ hp₁ hp₂ => rw [add_mul]; exact V.add_mem hp₁ hp₂
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← smul_eq_C_mul]
      exact V.smul_mem _ (hpow n q hq)
  let J : Ideal ℂ[X] :=
    { carrier := V
      zero_mem' := V.zero_mem
      add_mem' := V.add_mem
      smul_mem' := fun p q hq => hmul p q hq }
  let g := Submodule.IsPrincipal.generator J
  have hg : g ∈ J := Submodule.IsPrincipal.generator_mem J
  have hnr (z : ℂ) : g.eval z ≠ 0 := by
    obtain ⟨p, hp, hpz⟩ := hcover z
    have hpJ : p ∈ J := Submodule.subset_span hp
    have hd : g ∣ p := Ideal.mem_span_singleton.mp ((Ideal.span_singleton_generator J).symm ▸ hpJ)
    rintro hz
    obtain ⟨q, rfl⟩ := hd
    rw [eval_mul, hz, zero_mul] at hpz
    exact hpz rfl
  have hdeg : g.degree = 0 := by
    by_contra hdeg
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root g hdeg
    exact hnr z hz
  have hconst : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero (natDegree_eq_of_degree_eq_some hdeg)
  have hc : g.coeff 0 ≠ 0 := by
    simpa only [coeff_zero_eq_eval_zero] using hnr 0
  have hone : C (g.coeff 0)⁻¹ * g = 1 := by
    calc
      _ = C (g.coeff 0)⁻¹ * C (g.coeff 0) := congrArg (C (g.coeff 0)⁻¹ * ·) hconst
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, map_one]
  have hJ := J.mul_mem_left (C (g.coeff 0)⁻¹) hg
  rw [hone] at hJ
  exact hJ

/-- A pointwise covering family of polynomial normalized values generates a finite sum of
ordinary normalizations equal to one if it permits scalars and its span is stable under
multiplication by the spectral variable. -/
def OrdinaryPolynomialGenerationStatement : Prop :=
  ∀ {Test : Type*} (I : Test → ℂ → ℂ) (L : ReciprocalEntire),
    let S : Set ℂ[X] := IsOrdinaryNormalizationPolynomial I L
    (∀ s : ℂ, ∃ p ∈ S, p.eval s ≠ 0) →
    (∀ (c : ℂ) (p : ℂ[X]), p ∈ S → c • p ∈ S) →
    (∀ p ∈ S, X * p ∈ Submodule.span ℂ S) →
    HasFiniteOrdinaryNormalizationSum I L

theorem ordinaryPolynomialGeneration : OrdinaryPolynomialGenerationStatement := by
  classical
  intro Test I L S hcover hscale hX
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_iff_linearCombination ℂ S 1).mp
    (one_mem_span_of_polynomial_cover S hcover hX)
  let ι := {p : S // p ∈ c.support}
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let p (j : Fin (Fintype.card ι)) : ℂ[X] := c (e j).val • (e j).val.val
  have hp (j : Fin (Fintype.card ι)) : p j ∈ S := hscale _ _ (e j).val.2
  have hpoly : ∑ j, p j = 1 := by
    calc
      _ = ∑ q : ι, c q.val • q.val.val := Equiv.sum_comp e _
      _ = c.sum (fun q a => a • q.val) := by
        change ∑ q : {p : S // p ∈ c.support}, c q.val • q.val.val = _
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach c.support (fun q : S => c q • q.val)
      _ = 1 := by simpa only [Finsupp.linearCombination_apply] using hc
  choose i N hN using hp
  refine ⟨_, i, N, fun s => ?_⟩
  simp_rw [hN]
  simpa only [eval_finsetSum, eval_one] using congrArg (eval s) hpoly

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

private def scaleNormalization {I J L : ℂ → ℂ} (c : ℂ) (N : OrdinaryIntegralNormalization I L)
    (h : ∀ s, J s = c * I s) : OrdinaryIntegralNormalization J L where
  value s := c * N.value s
  analytic s hs := analyticAt_const.mul (N.analytic s hs)
  eq_on_right := by
    obtain ⟨b, hb⟩ := N.eq_on_right
    exact ⟨b, fun s hs => by rw [h s, hb s hs, mul_assoc]⟩

/-- Scalars on polynomial-valued complex equal-rank normalizations are realized by
scalars on the first Whittaker coefficient, with the same Schwartz test. -/
theorem isOrdinaryNormalizationPolynomial_complexEqual_smul (r : ℕ)
    (d e : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (c : ℂ) {p : ℂ[X]}
    (hp : IsOrdinaryNormalizationPolynomial (complexOrdinaryEqualTest r d e a D)
      (complexPairLFactor d e) p) :
    IsOrdinaryNormalizationPolynomial (complexOrdinaryEqualTest r d e a D)
      (complexPairLFactor d e) (c • p) := by
  obtain ⟨⟨W, V, Φ⟩, N, hN⟩ := hp
  let j := (c • W, V, Φ)
  have hj (s : ℂ) : complexOrdinaryEqualTest r d e a D j s =
      c * complexOrdinaryEqualTest r d e a D (W, V, Φ) s := by
    simp only [j, complexOrdinaryEqualTest, complexEqualIntegral, ArchimedeanLocal.equalIntegral,
      ArchimedeanLocal.equalIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul]
  refine ⟨j, scaleNormalization c N hj, fun s => ?_⟩
  change c * N.value s = (c • p).eval s
  rw [hN, smul_eq_C_mul, eval_mul, eval_C]

/-- Scalars on polynomial-valued complex unequal-rank normalizations are realized by
scalars on the larger Whittaker coefficient. -/
theorem isOrdinaryNormalizationPolynomial_complexUnequal_smul {r t : ℕ} (h : t < r)
    (d e : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (c : ℂ) {p : ℂ[X]}
    (hp : IsOrdinaryNormalizationPolynomial (complexOrdinaryUnequalTest h d e a D)
      (complexPairLFactor d e) p) :
    IsOrdinaryNormalizationPolynomial (complexOrdinaryUnequalTest h d e a D)
      (complexPairLFactor d e) (c • p) := by
  obtain ⟨⟨W, V⟩, N, hN⟩ := hp
  let j := (c • W, V)
  have hj (s : ℂ) : complexOrdinaryUnequalTest h d e a D j s =
      c * complexOrdinaryUnequalTest h d e a D (W, V) s := by
    simp only [j, complexOrdinaryUnequalTest, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral,
      ArchimedeanLocal.unequalIntegrand, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul]
  refine ⟨j, scaleNormalization c N hj, fun s => ?_⟩
  change c * N.value s = (c • p).eval s
  rw [hN, smul_eq_C_mul, eval_mul, eval_C]

end Langlands.Global.RankinSelbergGlobal
