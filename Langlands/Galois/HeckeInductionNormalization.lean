import Langlands.Galois.HeckeCharacterGaloisInductionStatement
import Langlands.Galois.UnitaryNormalization
import Langlands.Global.HeckeNormPower
import Langlands.Automorphic.Unramified.InductionBaseChangeHeckeFamily

/-!
# Unitary normalization of induced Euler polynomials of `χ · ‖·‖^{b/2}`

Let `χ` be a unitary Hecke character of `E` and `E/K` an extension of number fields. At an
unramified base place `v` with residue cardinality `q`, the factor of the induction of
`χ · ‖·‖^{b/2}` at a place `w | v` of residue degree `f` is `1 - χ_w(ϖ_w) (r X)^f` with
`r = q^{-b/2}`. Its reciprocal roots have absolute value `r`, so the raw Euler polynomial has
weight `-b`, and dividing every reciprocal root by its absolute value recovers the Euler
polynomial of the induction of `χ`.
-/

noncomputable section

universe uE uK

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Polynomial Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.Unramified.WeakInduction
open Langlands.Cohomology.Weights
open scoped Valued

section Polynomials

/-- A polynomial with nonzero constant coefficient is recovered by reversing twice. -/
theorem reverse_reverse_of_coeff_zero_ne {R : Type*} [Semiring R] {p : R[X]}
    (h : p.coeff 0 ≠ 0) : p.reverse.reverse = p := by
  ext n
  rw [coeff_reverse, coeff_reverse, reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (Or.inr h), Nat.sub_zero, revAt_invol]

/-- Reversal commutes with an injective coefficient map. -/
theorem reverse_map_of_injective {R S : Type*} [Semiring R] [Semiring S] {f : R →+* S}
    (hf : Function.Injective f) (p : R[X]) : (p.map f).reverse = p.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem reverse_one_sub_C_mul_X_pow {a : ℂ} (ha : a ≠ 0) {f : ℕ} (hf : f ≠ 0) :
    (1 - C a * X ^ f).reverse = X ^ f - C a := by
  have hdeg : (1 - C a * X ^ f).natDegree = f := by
    rw [show (1 - C a * X ^ f : ℂ[X]) = C (-a) * X ^ f + 1 by rw [C_neg]; ring,
      natDegree_add_eq_left_of_natDegree_lt]
    · exact natDegree_C_mul_X_pow f (-a) (neg_ne_zero.mpr ha)
    · rw [natDegree_C_mul_X_pow f (-a) (neg_ne_zero.mpr ha), natDegree_one]
      exact Nat.pos_of_ne_zero hf
  rw [reverse, hdeg, reflect_sub, reflect_one, reflect_C_mul_X_pow, revAt_le le_rfl,
    Nat.sub_self, pow_zero, mul_one]

theorem reverse_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (hf : ∀ i, f i ≠ 0) :
    (∏ i ∈ s, (1 - C (a i) * X ^ f i)).reverse = ∏ i ∈ s, (X ^ f i - C (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert j s hjs ih =>
    rw [Finset.prod_insert hjs, Finset.prod_insert hjs, reverse_mul_of_domain, ih,
      reverse_one_sub_C_mul_X_pow (ha j) (hf j)]

/-- The roots of a product of `X ^ f - a` with `‖a‖ = r ^ f` all have absolute value `r`. -/
theorem norm_eq_of_mem_roots_prod {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → ℕ)
    (hf : ∀ i, f i ≠ 0) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, ‖a i‖ = r ^ f i) {z : ℂ}
    (hz : z ∈ (∏ i ∈ s, (X ^ f i - C (a i))).roots) : ‖z‖ = r := by
  have hne : (∏ i ∈ s, (X ^ f i - C (a i))) ≠ 0 :=
    (monic_prod_of_monic s _ (fun i _ => monic_X_pow_sub_C (a i) (hf i))).ne_zero
  rw [mem_roots hne, IsRoot, eval_prod, Finset.prod_eq_zero_iff] at hz
  obtain ⟨i, _, hi⟩ := hz
  rw [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hi
  have h := congrArg norm hi
  rw [norm_pow, ha i] at h
  exact (pow_left_inj₀ (norm_nonneg z) hr (hf i)).mp h

/-- Normalizing the reciprocal roots of `∏ (1 - c_i (r X)^{f_i})`, with unitary `c_i` and
`r = radius q w`, gives `∏ (1 - c_i X^{f_i})`; the reversed polynomial has weight `w`. -/
theorem unitaryEulerPolynomial_prod_scaled {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℕ)
    (hc : ∀ i, ‖c i‖ = 1) (hf : ∀ i, f i ≠ 0) (q : ℕ) (hq : 0 < q) (w : ℤ) :
    unitaryEulerPolynomial (∏ i ∈ s, (1 - C (c i * (radius q w : ℂ) ^ f i) * X ^ f i)) =
        ∏ i ∈ s, (1 - C (c i) * X ^ f i) ∧
      HasComplexRootsOfWeight q w
        (∏ i ∈ s, (1 - C (c i * (radius q w : ℂ) ^ f i) * X ^ f i)).reverse ∧
      (∏ i ∈ s, (1 - C (c i * (radius q w : ℂ) ^ f i) * X ^ f i)).coeff 0 = 1 := by
  set r : ℝ := radius q w with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hq) _
  have hc0 : ∀ i, c i ≠ 0 := fun i h => by simpa [h] using hc i
  have ha0 : ∀ i, c i * (r : ℂ) ^ f i ≠ 0 := fun i =>
    mul_ne_zero (hc0 i) (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hrpos.ne'))
  have hanorm : ∀ i, ‖c i * (r : ℂ) ^ f i‖ = r ^ f i := fun i => by
    rw [norm_mul, hc i, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
  set P := ∏ i ∈ s, (1 - C (c i * (r : ℂ) ^ f i) * X ^ f i) with hP
  have hrev : P.reverse = ∏ i ∈ s, (X ^ f i - C (c i * (r : ℂ) ^ f i)) :=
    reverse_prod_one_sub s _ f ha0 hf
  have hmonic : P.reverse.Monic := by
    rw [hrev]
    exact monic_prod_of_monic s _ (fun i _ => monic_X_pow_sub_C _ (hf i))
  have hweight : HasComplexRootsOfWeight q w P.reverse := by
    intro z hz
    rw [hrev] at hz
    exact norm_eq_of_mem_roots_prod s _ f hf hrpos.le hanorm hz
  have hcoeff : P.coeff 0 = 1 := by
    rw [hP, coeff_zero_eq_eval_zero, eval_prod]
    exact Finset.prod_eq_one fun i _ => by simp [hf i]
  refine ⟨?_, hweight, hcoeff⟩
  rw [unitaryEulerPolynomial, unitaryEulerFromEigenvalues_eq_weight_substitution hmonic hweight,
    reverse_reverse_of_coeff_zero_ne (by rw [hcoeff]; exact one_ne_zero), hP, prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  simp only [sub_comp, one_comp, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
    ← C_mul]
  congr 3
  rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr0), mul_one]

end Polynomials

section Hecke

variable {K : Type uK} {E : Type uE} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E]

open scoped NumberField

/-- The norm of a uniformizer of a finite completion is the inverse absolute norm. -/
theorem norm_uniformizer (w : FinitePlace E) {π : FiniteCompletion E w}
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    ‖π‖ = (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, hπ,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp

/-- The value of `‖·‖^{b/2}` at a uniformizer above `v` is `radius q_v (-b)` to the power of the
residue degree. -/
theorem normPower_uniformizer (b : ℕ) (v : FinitePlace K) (w : FinitePlacesAbove E v)
    (π : (FiniteCompletion E w.1)ˣ)
    (hπ : Valued.v (π : FiniteCompletion E w.1) = WithZero.exp (-1 : ℤ)) :
    ((HeckeCharacter.normPower E ((b : ℂ) / 2)).finiteComponent w.1 π : ℂ) =
      (radius (residueCardinality v) (-(b : ℤ)) : ℂ) ^ w.1.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.1.asIdeal.LiesOver v.asIdeal := w.2
  have hcard : Ideal.absNorm w.1.asIdeal =
      residueCardinality v ^ w.1.asIdeal.inertiaDeg (𝓞 K) := by
    let := w.1.isPrime
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.1.asIdeal).symm
  have hq : 0 < (residueCardinality v : ℝ) := by
    have : residueCardinality v ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero (by simpa using v.ne_bot)⟩
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [HeckeCharacter.normPower_finiteComponent, norm_uniformizer w.1 hπ, hcard]
  set f := w.1.asIdeal.inertiaDeg (𝓞 K)
  have hreal : ((b : ℂ) / 2) * ((Real.log ((((residueCardinality v ^ f : ℕ) : ℝ))⁻¹) : ℝ) : ℂ) =
      (((b : ℝ) / 2 * Real.log ((((residueCardinality v ^ f : ℕ) : ℝ))⁻¹) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hreal, ← Complex.ofReal_exp, ← Complex.ofReal_pow]
  congr 1
  rw [Real.log_inv, Nat.cast_pow, Real.log_pow, radius, ← Real.rpow_natCast,
    ← Real.rpow_mul hq.le, Real.rpow_def_of_pos hq]
  congr 1
  push_cast
  ring

/-- Unitary normalization of the induction of `χ · ‖·‖^{b/2}` for a unitary `χ`. The raw
polynomials have constant coefficient one and reciprocal roots of weight `-b`. -/
theorem matchesHeckeInduction_normPower (χ : HeckeCharacter E) (hχ : χ.IsUnitary) (b : ℕ)
    (Q : FinitePlace K → ℂ[X])
    (hQ : MatchesHeckeInductionEulerPolynomials (K := K)
      (χ * HeckeCharacter.normPower E ((b : ℂ) / 2)) Q) :
    MatchesHeckeInductionEulerPolynomials (K := K) χ (fun v => unitaryEulerPolynomial (Q v)) ∧
      ∀ᶠ v : FinitePlace K in Filter.cofinite,
        (Q v).coeff 0 = 1 ∧
          HasComplexRootsOfWeight (residueCardinality v) (-(b : ℤ)) (Q v).reverse := by
  have hall : ∀ᶠ v : FinitePlace K in Filter.cofinite,
      IsUnramifiedAbove χ v ∧
        (∀ ϖ : ∀ w : FinitePlacesAbove E v, (FiniteCompletion E w.1)ˣ,
          IsUniformizerFamily v ϖ → unitaryEulerPolynomial (Q v) = inducedEulerPolynomial χ v ϖ) ∧
        (Q v).coeff 0 = 1 ∧
          HasComplexRootsOfWeight (residueCardinality v) (-(b : ℤ)) (Q v).reverse := by
    filter_upwards [hQ] with v hv
    obtain ⟨hun, heq⟩ := hv
    have hq : 0 < residueCardinality v := Nat.pos_of_ne_zero
      (Ideal.absNorm_ne_zero_of_nonZeroDivisors
        ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero (by simpa using v.ne_bot)⟩)
    have hcomp : ∀ ϖ : ∀ w : FinitePlacesAbove E v, (FiniteCompletion E w.1)ˣ,
        IsUniformizerFamily v ϖ →
        Q v = ∏ w : FinitePlacesAbove E v,
          (1 - C ((χ.finiteComponent w.1 (ϖ w) : ℂ) *
            (radius (residueCardinality v) (-(b : ℤ)) : ℂ) ^ w.1.asIdeal.inertiaDeg (𝓞 K)) *
            X ^ w.1.asIdeal.inertiaDeg (𝓞 K)) := by
      intro ϖ hϖ
      rw [heq ϖ hϖ, inducedEulerPolynomial]
      refine Finset.prod_congr rfl fun w _ => ?_
      have hmulv : (((χ * HeckeCharacter.normPower E ((b : ℂ) / 2)).finiteComponent w.1 (ϖ w) :
          ℂˣ) : ℂ) = (χ.finiteComponent w.1 (ϖ w) : ℂ) *
            ((HeckeCharacter.normPower E ((b : ℂ) / 2)).finiteComponent w.1 (ϖ w) : ℂ) := rfl
      rw [hmulv, normPower_uniformizer b v w (ϖ w) (hϖ w)]
    have hf : ∀ w : FinitePlacesAbove E v, w.1.asIdeal.inertiaDeg (𝓞 K) ≠ 0 := fun w => by
      let := w.1.isPrime
      exact (Ideal.inertiaDeg_pos w.1.asIdeal (𝓞 K)).ne'
    have hunit : ∀ w : FinitePlacesAbove E v, ∀ x : (FiniteCompletion E w.1)ˣ,
        ‖(χ.finiteComponent w.1 x : ℂ)‖ = 1 := by
      intro w x
      change ‖(χ (finiteClassInclusion E w.1 x) : ℂ)‖ = 1
      exact hχ _
    have key (ϖ : ∀ w : FinitePlacesAbove E v, (FiniteCompletion E w.1)ˣ) :=
      unitaryEulerPolynomial_prod_scaled (Finset.univ : Finset (FinitePlacesAbove E v))
        (fun w : FinitePlacesAbove E v => (χ.finiteComponent w.1 (ϖ w) : ℂ))
        (fun w : FinitePlacesAbove E v => w.1.asIdeal.inertiaDeg (𝓞 K))
        (fun w : FinitePlacesAbove E v => hunit w (ϖ w)) hf
        (residueCardinality v) hq (-(b : ℤ))
    obtain ⟨ϖ₀, hϖ₀⟩ : ∃ ϖ : ∀ w : FinitePlacesAbove E v, (FiniteCompletion E w.1)ˣ,
        IsUniformizerFamily v ϖ := by
      choose ϖ hϖ using fun w : FinitePlacesAbove E v =>
        Automorphic.Unramified.WeakInduction.exists_uniformizer w.1
      exact ⟨ϖ, hϖ⟩
    refine ⟨fun w => ⟨(hun w).1, fun x hx => ?_⟩, fun ϖ hϖ => ?_, ?_, ?_⟩
    · have h1 := (hun w).2 x hx
      have h2 := HeckeCharacter.normPower_isUnramifiedAt E ((b : ℂ) / 2) w.1 x hx
      change χ.finiteComponent w.1 x *
        (HeckeCharacter.normPower E ((b : ℂ) / 2)).finiteComponent w.1 x = 1 at h1
      rw [h2, mul_one] at h1
      exact h1
    · rw [hcomp ϖ hϖ, (key ϖ).1, inducedEulerPolynomial]
    · rw [hcomp ϖ₀ hϖ₀]
      exact (key ϖ₀).2.2
    · rw [hcomp ϖ₀ hϖ₀]
      exact (key ϖ₀).2.1
  refine ⟨?_, ?_⟩
  · filter_upwards [hall] with v hv
    exact ⟨hv.1, hv.2.1⟩
  · filter_upwards [hall] with v hv
    exact hv.2.2

end Hecke

end Langlands.GaloisRepresentation
