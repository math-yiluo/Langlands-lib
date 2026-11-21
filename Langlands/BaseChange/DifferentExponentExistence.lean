import Langlands.BaseChange.DifferentIdealComparison
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Existence of the trace-codifferent exponent -/

noncomputable section

set_option autoImplicit false

open IsLocalRing ValuativeRel
open scoped nonZeroDivisors Langlands.ClassFieldTheory.Local

namespace Langlands.BaseChange

open ClassFieldTheory.Local (localIntegerAlgebra_finite localIntegerAlgebra_isIntegralClosure)

universe u v

/-- A continuous finite separable extension of local fields has a trace-codifferent exponent. -/
def DifferentExponentExistenceStatement : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E] [ValuativeRel F] [ValuativeRel E]
    [TopologicalSpace F] [TopologicalSpace E] [IsNonarchimedeanLocalField F]
    [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E],
    Continuous (algebraMap F E) → ∃ d, IsDifferentExponent F E d

set_option maxHeartbeats 700000 in
/-- The different is a nonzero integral ideal of a DVR. Inverting its uniformizer power
identifies the trace-dual fractional ideal with the codifferent in the statement. -/
theorem differentExponentExistence : DifferentExponentExistenceStatement.{u, v} := by
  intro F E _ _ _ _ _ _ _ _ _ _ _ _ hcont
  let := localIntegerAlgebra_isIntegralClosure F E hcont
  let := localIntegerAlgebra_finite F E hcont
  let : IsFractionRing (𝒪[F]) F := (Valuation.integer.integers (valuation F)).isFractionRing
  let : IsFractionRing (𝒪[E]) E := (Valuation.integer.integers (valuation E)).isFractionRing
  have hcoe := coeIdeal_differentIdeal (𝒪[F]) F E (𝒪[E])
  have hne : differentIdeal (𝒪[F]) (𝒪[E]) ≠ ⊥ := by
    intro heq
    rw [heq, FractionalIdeal.coeIdeal_bot] at hcoe
    exact (inv_ne_zero (FractionalIdeal.dual_ne_zero (𝒪[F]) F one_ne_zero)) hcoe.symm
  obtain ⟨d, hd⟩ := exists_maximalIdeal_pow_eq_of_principal (𝒪[E])
    (IsPrincipalIdealRing.principal _) (differentIdeal (𝒪[F]) (𝒪[E])) hne
  obtain ⟨ϖ, hϖ⟩ := GeneralLinear.Iwasawa.exists_isUniformizingElement E
  have hpow : (ϖ : E) ^ d ≠ 0 := pow_ne_zero d ϖ.ne_zero
  rw [hd, Conductor.maximalIdeal_pow_eq_span_jacquetUniformizer _ ϖ hϖ d,
    FractionalIdeal.coeIdeal_span_singleton] at hcoe
  have hdual := congrArg (fun J : FractionalIdeal (𝒪[E])⁰ E => J⁻¹) hcoe.symm
  rw [inv_inv, FractionalIdeal.spanSingleton_inv] at hdual
  refine ⟨d, ϖ, hϖ, fun x => ?_⟩
  have hone (y : E) : y ∈ (1 : FractionalIdeal (𝒪[E])⁰ E) ↔ y ∈ 𝒪[E] := by
    rw [FractionalIdeal.mem_one_iff]
    change y ∈ (𝒪[E]).subtype.range ↔ y ∈ 𝒪[E]
    rw [Subring.range_subtype]
  have hrange : (algebraMap (𝒪[F]) F).range = 𝒪[F] := Subring.range_subtype _
  have hmem : x ∈ FractionalIdeal.dual (𝒪[F]) F (1 : FractionalIdeal (𝒪[E])⁰ E) ↔
      ∀ y ∈ 𝒪[E], Algebra.trace F E (x * y) ∈ 𝒪[F] := by
    simp only [FractionalIdeal.mem_dual one_ne_zero, hone, hrange, Algebra.traceForm_apply]
  rw [← hmem, hdual, FractionalIdeal.mem_spanSingleton]
  constructor
  · rintro ⟨z, hz⟩
    change (z : E) * ((ϖ : E) ^ d)⁻¹ = x at hz
    rw [← hz, mul_assoc, inv_mul_cancel₀ hpow, mul_one]
    exact z.property
  · intro hx
    refine ⟨⟨x * (ϖ : E) ^ d, hx⟩, ?_⟩
    change x * (ϖ : E) ^ d * ((ϖ : E) ^ d)⁻¹ = x
    rw [mul_assoc, mul_inv_cancel₀ hpow, mul_one]

end Langlands.BaseChange
