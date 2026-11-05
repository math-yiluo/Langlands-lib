import Langlands.AlgebraicGeometry.FlatIntegralPureDimensionStatement
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one

/-! # Componentwise pure dimension for flat integral extensions -/

universe u v

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

open P2MW.S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one.P2mNormOpen

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Flat contraction sends every minimal prime to a minimal prime. -/
theorem under_mem_minimalPrimes_of_flat [Module.Flat R S]
    (q : Ideal S) (hq : q ∈ minimalPrimes S) : q.under R ∈ minimalPrimes R := by
  have : q.IsPrime := hq.1.1
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro p ⟨hp, _⟩ hpq
  have := hp
  obtain ⟨Q, hQq, hQ, hQp⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := q.under R) q hpq
  have := hQ
  have := hQp
  have heq : Q = q := hQq.antisymm (hq.2 ⟨hQ, bot_le⟩ hQq)
  exact le_of_eq (by rw [← heq]; exact (Q.over_def p).symm)

/-- Every quotient by a contracted ideal has the same dimension as its
upstairs quotient for an integral algebra extension. -/
theorem ringKrullDim_quotient_under_eq_of_integral [Algebra.IsIntegral R S]
    (q : Ideal S) : ringKrullDim (R ⧸ q.under R) = ringKrullDim (S ⧸ q) := by
  exact ringKrullDim_eq_of_ringHom_isIntegral_of_injective
    (Ideal.quotientMap q (algebraMap R S) le_rfl)
    (RingHom.IsIntegral.quotient (algebraMap R S) Algebra.IsIntegral.isIntegral)
    Ideal.quotientMap_injective

/-- The exact universal invariance proposition. -/
theorem flatIntegralPureRingDimensionInvariance :
    FlatIntegralPureRingDimensionInvariance.{u,v} := by
  intro R S _ _ _ _ _ _ d
  constructor
  · intro h q hq
    exact (ringKrullDim_quotient_under_eq_of_integral q).symm.trans
      (h _ (under_mem_minimalPrimes_of_flat q hq))
  · intro h p hp
    have hinj : Function.Injective (algebraMap R S) :=
      (faithfulSMul_iff_algebraMap_injective R S).mp inferInstance
    have hp' : p ∈ ((⊥ : Ideal S).comap (algebraMap R S)).minimalPrimes := by
      rwa [Ideal.comap_bot_of_injective _ hinj]
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) p hp'
    rw [← hqp]
    exact (ringKrullDim_quotient_under_eq_of_integral q).trans (h q hq)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
