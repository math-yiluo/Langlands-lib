import Langlands.Algebra.HarishChandra.VermaProjection
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Central characters of mirror Verma modules

For a sorted weight basis of `𝔤`, an element `z` of `U(𝔤)` commuting with `𝔥` is congruent to a
scalar modulo the Verma right ideal attached to scalars `c`. That scalar is a polynomial function
of `c` along every affine line. This file also proves the two facts used to compare scalars
through singular vectors. If `z` is central and `u₀ ∉ R` maps a second Verma right ideal into
`R`, the two scalars agree. And the element of the span of the negative monomials that lie in
`R + v₀ U`, for a singular `v₀`, are the products `v₀ y` with `y` in that span. -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open Langlands.Algebra.UniversalEnveloping Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

section Abstract

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Comparison of scalars through a vector: if `z` commutes with `u₀`, acts by `s₁` modulo a right
ideal `R`, and `u₀ (z - s₂) ∈ R`, then `s₁ = s₂` unless `u₀ ∈ R`. -/
theorem eq_of_sub_mem_of_mul_sub_mem (R : Submodule ℂ A) (hR : ∀ r ∈ R, ∀ y : A, r * y ∈ R)
    (z u₀ : A) (hzu : z * u₀ = u₀ * z) (s₁ s₂ : ℂ) (h₁ : z - algebraMap ℂ A s₁ ∈ R)
    (h₂ : u₀ * (z - algebraMap ℂ A s₂) ∈ R) (hu₀ : u₀ ∉ R) : s₁ = s₂ := by
  by_contra hne
  apply hu₀
  have h3 := hR _ h₁ u₀
  have h4 : (s₂ - s₁) • u₀ ∈ R := by
    have heq : (s₂ - s₁) • u₀ = (z - algebraMap ℂ A s₁) * u₀ - u₀ * (z - algebraMap ℂ A s₂) := by
      rw [sub_mul, mul_sub, hzu, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_smul]
      abel
    rw [heq]
    exact R.sub_mem h3 h₂
  have h5 := R.smul_mem (s₂ - s₁)⁻¹ h4
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hne)), one_smul] at h5

end Abstract

section Sorted

open scoped Classical

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

variable {H : LieSubalgebra ℂ L} {n : ℕ} (b : Module.Basis (Fin n) ℂ L)
  (w : Fin n → H → ℂ) (hw : ∀ a (h : H), ⁅(h : L), b a⁆ = w a h • b a) (X : H)
  (hzero : ∀ a, realWeight w X a = 0 → b a ∈ H ∧ w a = 0)
  (hd : Antitone (realWeight w X))

/-- The scalar of the projection of a monomial without positive letters and with only letters of
weight zero, as a polynomial in the parameter `t` of the affine line `c₀ + t c₁`. -/
def vermaMonomialPolynomial (c₀ c₁ : Fin n → ℂ) (e : Fin n → ℕ) : ℂ[X] :=
  if ∀ i, e i ≠ 0 → realWeight w X i = 0 then
    ∏ i, if realWeight w X i = 0 then (C (c₀ i) + C (c₁ i) * Polynomial.X) ^ e i else 1
  else 0

theorem vermaProjection_monomial_eq (c : Fin n → ℂ) (e : Fin n → ℕ)
    (he : ∀ i, e i ≠ 0 → realWeight w X i = 0) :
    vermaProjection b w X c (orderedPBWMonomial b e) =
      algebraMap ℂ U (∏ i, if realWeight w X i = 0 then c i ^ e i else 1) := by
  have hpos : ¬ ∃ i, e i ≠ 0 ∧ 0 < realWeight w X i := by
    rintro ⟨i, hi, hdi⟩
    rw [he i hi] at hdi
    exact lt_irrefl 0 hdi
  have hneg : (fun i => if realWeight w X i < 0 then e i else 0) = fun _ => 0 := by
    funext i
    by_cases hi : realWeight w X i < 0
    · rw [ite_eq_left hi]
      by_contra hei
      rw [he i hei] at hi
      exact lt_irrefl 0 hi
    · rw [ite_eq_right hi]
  rw [vermaProjection_monomial, vermaProjectionValue, ite_eq_right hpos, hneg,
    orderedPBWMonomial_zero, Algebra.algebraMap_eq_smul_one]

include hw hzero hd in
/-- An element commuting with `𝔥` is congruent to a scalar modulo the Verma right ideal, and along
an affine line of parameters the scalar is a polynomial in the parameter. -/
theorem exists_polynomial_sub_mem_basisVermaIdeal (z : U)
    (hz : ∀ h : H, commutatorMap (h : L) z = 0) (c₀ c₁ : Fin n → ℂ) :
    ∃ P : ℂ[X], ∀ t : ℂ,
      z - algebraMap ℂ U (P.eval t) ∈ basisVermaIdeal b w X (c₀ + t • c₁) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp
    (mem_sup_of_commute_of_antitone b w hw X hd z hz)
  have hq' := realZeroGeneratorSubalgebra_le b w hw X hq
  obtain ⟨f, hfsupp, hfq⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hq'
  refine ⟨∑ e ∈ f.support, C (f e) * vermaMonomialPolynomial w X c₀ c₁ e, fun t => ?_⟩
  have hpR : p ∈ basisVermaIdeal b w X (c₀ + t • c₁) :=
    Submodule.mem_sup_left (realPositiveLetterSpan_le_generatorSpan b w X hd
      (realPositiveGeneratorSpan_le b w hw X hd hp))
  have hqR := sub_vermaProjection_mem b w hw X (c₀ + t • c₁) hzero hd q
  have hπq : vermaProjection b w X (c₀ + t • c₁) q =
      algebraMap ℂ U ((∑ e ∈ f.support, C (f e) * vermaMonomialPolynomial w X c₀ c₁ e).eval t) := by
    rw [← hfq, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have he' : ∀ i, e i ≠ 0 → realWeight w X i = 0 := hfsupp he
    rw [map_smul, orderedPBWBasisOf_apply, vermaProjection_monomial_eq b w X _ e he', eval_mul,
      eval_C, vermaMonomialPolynomial, ite_eq_left he', eval_prod, map_mul,
      Algebra.algebraMap_eq_smul_one (f e), smul_mul_assoc, one_mul]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : realWeight w X i = 0
    · rw [ite_eq_left hi, ite_eq_left hi, eval_pow, eval_add, eval_mul, eval_C, eval_C, eval_X,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm t]
    · rw [ite_eq_right hi, ite_eq_right hi, eval_one]
  rw [← hπq, add_sub_assoc]
  exact Submodule.add_mem _ hpR hqR

include hzero hd in
/-- A scalar lies in the Verma right ideal only if it is zero. -/
theorem eq_zero_of_algebraMap_mem_basisVermaIdeal (hw' : ∀ a (h : H), ⁅(h : L), b a⁆ = w a h • b a)
    (c : Fin n → ℂ) (s : ℂ) (hs : algebraMap ℂ U s ∈ basisVermaIdeal b w X c) : s = 0 := by
  have h1 := vermaProjection_eq_zero_of_mem_basisVermaIdeal b w hw' X c hzero hd hs
  have h2 : vermaProjection b w X c (algebraMap ℂ U s) = algebraMap ℂ U s := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← orderedPBWMonomial_zero b,
      vermaProjection_monomial_of_neg b w X c _ (fun i hi => absurd rfl hi)]
  rw [h2] at h1
  have h3 := congrArg (fun u => (orderedPBWBasisOf b).repr u (fun _ => 0)) h1
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_zero, Finsupp.smul_apply,
    Finsupp.zero_apply] at h3
  rw [← orderedPBWMonomial_zero b, ← orderedPBWBasisOf_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h3
  exact h3

/-- A singular vector: if `u₀` multiplies every generator of a Verma right ideal into a right ideal
`R`, it multiplies the whole Verma right ideal into `R`. -/
theorem mul_mem_of_basisVermaIdeal (c : Fin n → ℂ) (R : Submodule ℂ U)
    (hR : ∀ r ∈ R, ∀ y : U, r * y ∈ R) (u₀ : U)
    (hpos : ∀ a, 0 < realWeight w X a → u₀ * ι (b a) ∈ R)
    (hzer : ∀ a, realWeight w X a = 0 → u₀ * (ι (b a) - algebraMap ℂ U (c a)) ∈ R) {r : U}
    (hr : r ∈ basisVermaIdeal b w X c) : u₀ * r ∈ R := by
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hr
  clear hr
  rw [mul_add]
  refine R.add_mem ?_ ?_
  · induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, rfl⟩ := hx
      rw [← mul_assoc]
      exact hR _ (hpos a ha) v
    | zero => rw [mul_zero]; exact R.zero_mem
    | add x y _ _ h₁ h₂ => rw [mul_add]; exact R.add_mem h₁ h₂
    | smul t x _ h => rw [mul_smul_comm]; exact R.smul_mem t h
  · induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, rfl⟩ := hx
      rw [← mul_assoc]
      exact hR _ (hzer a ha) v
    | zero => rw [mul_zero]; exact R.zero_mem
    | add x y _ _ h₁ h₂ => rw [mul_add]; exact R.add_mem h₁ h₂
    | smul t x _ h => rw [mul_smul_comm]; exact R.smul_mem t h

theorem realNegativeLetterSpan_mul_mem (hneg : ∀ a a', realWeight w X a < 0 →
      realWeight w X a' < 0 →
      ⁅b a, b a'⁆ ∈ Submodule.span ℂ (b '' {i | realWeight w X i < 0}))
    {x y : U} (hx : x ∈ realNegativeLetterSpan b w X) (hy : y ∈ realNegativeLetterSpan b w X) :
    x * y ∈ realNegativeLetterSpan b w X := by
  have hle := adjoin_le_span_orderedPBWBasisOf b (fun a => realWeight w X a < 0) hneg
  have hsub : realNegativeLetterSpan b w X ≤
      (Algebra.adjoin ℂ {u | ∃ a, realWeight w X a < 0 ∧ u = ι (b a)}).toSubmodule := by
    rw [realNegativeLetterSpan, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    rw [orderedPBWBasisOf_apply, orderedPBWMonomial]
    exact ofFn_prod_pow_mem_adjoin (k := ℂ) _ (fun a => realWeight w X a < 0) e he
  exact hle (Subalgebra.mul_mem _ (hsub hx) (hsub hy))

/-- The projection takes values in the span of the negative monomials. -/
theorem vermaProjection_mem_realNegativeLetterSpan (c : Fin n → ℂ) (x : U) :
    vermaProjection b w X c x ∈ realNegativeLetterSpan b w X := by
  rw [← (orderedPBWBasisOf b).linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [orderedPBWBasisOf_apply, vermaProjection_monomial, vermaProjectionValue]
  split_ifs
  · exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _
      (Submodule.subset_span ⟨fun i => if realWeight w X i < 0 then e i else 0, fun i hi => ?_,
        orderedPBWBasisOf_apply _ _⟩)
    by_contra h
    exact hi (by simp [h])

include hw hzero hd in
/-- Elements of the span of the negative monomials that lie in `R + v₀ U`, for a singular
`v₀` in that span, are products `v₀ y` with `y` in the span. Here `R` is the Verma right ideal for
`c` and `v₀` maps the Verma right ideal for `c'` into it. -/
theorem exists_eq_mul_of_mem_sup (hneg : ∀ a a', realWeight w X a < 0 →
      realWeight w X a' < 0 →
      ⁅b a, b a'⁆ ∈ Submodule.span ℂ (b '' {i | realWeight w X i < 0}))
    (c c' : Fin n → ℂ) (v₀ : U)
    (hv₀ : v₀ ∈ realNegativeLetterSpan b w X)
    (hsing : ∀ r ∈ basisVermaIdeal b w X c', v₀ * r ∈ basisVermaIdeal b w X c) {u : U}
    (hu : u ∈ realNegativeLetterSpan b w X)
    (hmem : ∃ r ∈ basisVermaIdeal b w X c, ∃ x : U, u = r + v₀ * x) :
    ∃ y ∈ realNegativeLetterSpan b w X, u = v₀ * y := by
  obtain ⟨r, hr, x, rfl⟩ := hmem
  refine ⟨vermaProjection b w X c' x, vermaProjection_mem_realNegativeLetterSpan b w X c' x, ?_⟩
  · have hx := sub_vermaProjection_mem b w hw X c' hzero hd x
    have h1 : r + v₀ * x - v₀ * vermaProjection b w X c' x ∈ basisVermaIdeal b w X c := by
      rw [add_sub_assoc, ← mul_sub]
      exact Submodule.add_mem _ hr (hsing _ hx)
    have hπ := vermaProjection_eq_zero_of_mem_basisVermaIdeal b w hw X c hzero hd h1
    have hy := vermaProjection_mem_realNegativeLetterSpan b w X c' x
    rw [map_sub, vermaProjection_of_mem_realNegativeLetterSpan b w X c hu,
      vermaProjection_of_mem_realNegativeLetterSpan b w X c
        (realNegativeLetterSpan_mul_mem b w X hneg hv₀ hy), sub_eq_zero] at hπ
    exact hπ

end Sorted

end Langlands.Algebra.HarishChandra
