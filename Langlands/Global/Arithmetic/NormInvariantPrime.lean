import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois

/-! # Uniqueness of a prime cut out by an invariant norm -/

open NumberField IsDedekindDomain
open scoped Pointwise

namespace Langlands.Global.FieldRealization

universe u v w

/-- A prime cut out by a Galois-invariant norm is the unique prime over its restriction. -/
theorem prime_unique_of_norm_invariant
    {K : Type u} {L : Type v} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {E : Type w} [NontriviallyNormedField E]
    (j : L →+* E) (P : HeightOneSpectrum (𝓞 L))
    (hP : ∀ a : 𝓞 L, a ∈ P.asIdeal ↔ ‖j a‖ < 1)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), ‖j (σ x)‖ = ‖j x‖)
    (v : HeightOneSpectrum (𝓞 K)) [P.asIdeal.LiesOver v.asIdeal] :
    ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal → w = P := by
  intro w hw
  have := hw
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    v.asIdeal P.asIdeal w.asIdeal (L ≃ₐ[K] L)
  have hfix : σ • P.asIdeal = P.asIdeal := by
    ext a
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hP, hP]
    change ‖j (σ⁻¹ (a : L))‖ < 1 ↔ ‖j (a : L)‖ < 1
    rw [hinv]
  exact HeightOneSpectrum.ext (hσ.symm.trans hfix)

/-- The fiber over `v` has the distinguished unique point `P`. -/
abbrev normInvariantPrimeFiberUnique
    {K : Type u} {L : Type v} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {E : Type w} [NontriviallyNormedField E]
    (j : L →+* E) (P : HeightOneSpectrum (𝓞 L))
    (hP : ∀ a : 𝓞 L, a ∈ P.asIdeal ↔ ‖j a‖ < 1)
    (hinv : ∀ (σ : L ≃ₐ[K] L) (x : L), ‖j (σ x)‖ = ‖j x‖)
    (v : HeightOneSpectrum (𝓞 K)) [hPv : P.asIdeal.LiesOver v.asIdeal] :
    Unique {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} where
  default := ⟨P, hPv⟩
  uniq w := Subtype.ext (prime_unique_of_norm_invariant j P hP hinv v w.val w.property)

end Langlands.Global.FieldRealization
