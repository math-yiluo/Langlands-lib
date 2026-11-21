import Langlands.BaseChange.ExtensionInvariants
import Langlands.ClassFieldTheory.Local.LocalUnramifiedNorm
import Langlands.Representation.Conductor.JacquetScaledLevel
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Valuation.ValuationRing

/-! # The trace-codifferent exponent and different ideals in towers -/

noncomputable section

open IsLocalRing ValuativeRel
open scoped nonZeroDivisors Langlands.ClassFieldTheory.Local

namespace Langlands.BaseChange

open ClassFieldTheory.Local (localIntegerAlgebra_finite localIntegerAlgebra_isIntegralClosure
  localRamificationFactor map_maximalIdeal_eq_localRamificationFactor)

universe u v w

section Comparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E]

/-- The trace characterization of the different exponent computes the actual different ideal. -/
theorem IsDifferentExponent.differentIdeal_eq_maximalIdeal_pow {d : ℕ}
    (hd : IsDifferentExponent F E d) (hcont : Continuous (algebraMap F E)) :
    differentIdeal (𝒪[F]) (𝒪[E]) = maximalIdeal (𝒪[E]) ^ d := by
  let := localIntegerAlgebra_isIntegralClosure F E hcont
  let : IsFractionRing (𝒪[F]) F := (Valuation.integer.integers (valuation F)).isFractionRing
  let : IsFractionRing (𝒪[E]) E := (Valuation.integer.integers (valuation E)).isFractionRing
  obtain ⟨ϖ, hϖ, hcod⟩ := hd
  have hpow : (ϖ : E) ^ d ≠ 0 := pow_ne_zero d ϖ.ne_zero
  have hdual : FractionalIdeal.dual (𝒪[F]) F (1 : FractionalIdeal (𝒪[E])⁰ E) =
      FractionalIdeal.spanSingleton (𝒪[E])⁰ (((ϖ : E) ^ d)⁻¹) := by
    ext x
    rw [FractionalIdeal.mem_dual one_ne_zero, FractionalIdeal.mem_spanSingleton]
    have hone (y : E) : y ∈ (1 : FractionalIdeal (𝒪[E])⁰ E) ↔ y ∈ 𝒪[E] := by
      rw [FractionalIdeal.mem_one_iff]
      change y ∈ (𝒪[E]).subtype.range ↔ y ∈ 𝒪[E]
      rw [Subring.range_subtype]
    have hrange : (algebraMap (𝒪[F]) F).range = 𝒪[F] := Subring.range_subtype _
    simp only [hone, hrange, Algebra.traceForm_apply]
    rw [hcod x]
    constructor
    · intro hx
      refine ⟨⟨x * (ϖ : E) ^ d, hx⟩, ?_⟩
      change x * (ϖ : E) ^ d * ((ϖ : E) ^ d)⁻¹ = x
      rw [mul_assoc, mul_inv_cancel₀ hpow, mul_one]
    · rintro ⟨z, hz⟩
      change (z : E) * ((ϖ : E) ^ d)⁻¹ = x at hz
      rw [← hz, mul_assoc, inv_mul_cancel₀ hpow, mul_one]
      exact z.property
  apply (FractionalIdeal.coeIdeal_inj (K := E)).mp
  rw [coeIdeal_differentIdeal (𝒪[F]) F, hdual, FractionalIdeal.spanSingleton_inv, inv_inv,
    Conductor.maximalIdeal_pow_eq_span_jacquetUniformizer _ ϖ hϖ d,
    FractionalIdeal.coeIdeal_span_singleton]
  rfl

end Comparison

section Tower

variable {F : Type u} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {M : Type w} [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra F E] [Algebra F M] [Algebra E M] [IsScalarTower F E M]
  [ValuativeExtension F E] [ValuativeExtension F M] [ValuativeExtension E M]
  [FiniteDimensional F E] [FiniteDimensional F M] [FiniteDimensional E M]

/-- Transitivity expresses the difference of the two upper different exponents
as the base different exponent times the upper relative ramification index. -/
theorem IsDifferentExponent.differentIdeal_exponents_in_tower {d a b : ℕ}
    (hd : IsDifferentExponent F E d)
    (hFE : Continuous (algebraMap F E)) (hFM : Continuous (algebraMap F M))
    (hEM : Continuous (algebraMap E M))
    (ha : differentIdeal (𝒪[F]) (𝒪[M]) = maximalIdeal (𝒪[M]) ^ a)
    (hb : differentIdeal (𝒪[E]) (𝒪[M]) = maximalIdeal (𝒪[M]) ^ b) :
    a = b + localRamificationFactor E M * d := by
  let : IsScalarTower (𝒪[F]) (𝒪[E]) (𝒪[M]) :=
    .of_algebraMap_eq fun x => Subtype.ext (IsScalarTower.algebraMap_apply F E M (x : F))
  let := localIntegerAlgebra_finite F E hFE
  let := localIntegerAlgebra_finite F M hFM
  let := localIntegerAlgebra_finite E M hEM
  let : CharZero (𝒪[F]) := (𝒪[F]).subtype.charZero
  have htrans := differentIdeal_eq_differentIdeal_mul_differentIdeal
    (A := 𝒪[F]) (B := 𝒪[E]) (𝒪[M])
  rw [ha, hb, hd.differentIdeal_eq_maximalIdeal_pow hFE, Ideal.map_pow,
    map_maximalIdeal_eq_localRamificationFactor E M, ← pow_mul, ← pow_add] at htrans
  exact ((maximalIdeal (𝒪[M])).pow_right_strictAnti
    (IsDiscreteValuationRing.not_a_field _) (maximalIdeal.isMaximal _).ne_top).injective htrans

end Tower

end Langlands.BaseChange
