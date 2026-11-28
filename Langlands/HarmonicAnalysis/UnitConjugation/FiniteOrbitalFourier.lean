import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentParabolicOrbitalMeasure
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Fourier transforms of finite orbital measures -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open MeasureTheory QuotientIntegration

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
  [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]

/-- With a finite measure on the stabilizer quotient, all orbital integrals converge
absolutely and the Fourier-transformed distribution is represented by the integral of the
pairing character along the orbit. This density is continuous and bounded by the total mass. -/
def FiniteOrbitalFourierStatement : Prop :=
  haveI := IsModuleTopology.isTopologicalRing F A
  ∀ (X : A) [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X))) [IsFiniteMeasure ν]
    (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A)
    (hs : B.IsSymm) (hnd : B.Nondegenerate) (μ : AdditiveHaarMeasure A),
    ∃ hconv : OrbitalIntegralConverges X ν,
      let Θ Y := ∫ q, pairingCharacter ψ B (orbitalPoint X q) Y ∂ν
      Continuous Θ ∧ LocallyIntegrable Θ μ.measure ∧
        (∀ Y, ‖Θ Y‖ ≤ ν.real Set.univ) ∧ ∀ f : SchwartzBruhat A,
          distributionFourier ψ hs hnd μ (orbitalDistribution X ν hconv) f =
            ∫ Y, Θ Y * f Y ∂μ.measure

theorem finiteOrbitalFourier : FiniteOrbitalFourierStatement (F := F) (A := A) := by
  have := IsModuleTopology.isTopologicalRing F A
  have := secondCountableTopology_of_finiteDimensional F A
  have := locallyCompactSpace_of_finiteDimensional F A
  intro X _ _ ν _ ψ B hs hnd μ
  let Q := LeftQuotient (conjugationCentralizer X)
  have hOrb := continuous_orbitalPoint X
  have hconv : OrbitalIntegralConverges X ν := by
    intro f
    obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
    rw [orbitalIntegrand_eq_comp_orbitalPoint]
    exact (integrable_const C).mono (f.continuous.comp hOrb).measurable.aestronglyMeasurable
      (ae_of_all _ fun q => (hC (orbitalPoint X q)).trans (le_abs_self C))
  let χ (p : A × A) : ℂ := pairingCharacter ψ B p.1 p.2
  have hχ : Continuous χ :=
    ψ.continuous_complex.comp (IsModuleTopology.continuous_bilinear_of_finite_left B)
  have hχnorm (p : A × A) : ‖χ p‖ = 1 := ψ.norm_complex _
  let Θ (Y : A) : ℂ := ∫ q, χ (orbitalPoint X q, Y) ∂ν
  have hΘ : Continuous Θ := continuous_of_dominated
    (fun Y => (hχ.comp (hOrb.prodMk continuous_const)).measurable.aestronglyMeasurable)
    (fun Y => ae_of_all ν fun q => (hχnorm (orbitalPoint X q, Y)).le)
    (integrable_const (1 : ℝ))
    (ae_of_all ν fun q => hχ.comp (continuous_const.prodMk continuous_id))
  refine ⟨hconv, hΘ, hΘ.locallyIntegrable, ?_, ?_⟩
  · intro Y
    change ‖∫ q, χ (orbitalPoint X q, Y) ∂ν‖ ≤ _
    calc
      _ ≤ ∫ q, ‖χ (orbitalPoint X q, Y)‖ ∂ν := norm_integral_le_integral_norm _
      _ = ν.real Set.univ := by simp only [hχnorm, integral_const, smul_eq_mul, mul_one]
  · intro f
    let k (p : Q × A) := χ (orbitalPoint X p.1, p.2) * f p.2
    have hk : Measurable k :=
      (hχ.measurable.comp ((hOrb.measurable.comp measurable_fst).prodMk measurable_snd)).mul
        (f.continuous.measurable.comp measurable_snd)
    have hf := f.continuous.integrable_of_hasCompactSupport
      (μ := μ.measure) f.hasCompactSupport
    have hi : Integrable k (ν.prod μ.measure) :=
      (hf.comp_snd ν).mono hk.aestronglyMeasurable (ae_of_all _ fun p => by
        simp [k, hχnorm])
    rw [distributionFourier_apply, orbitalDistribution_apply, orbitalIntegrand_eq_comp_orbitalPoint]
    change (∫ q, pairingFourierSB ψ hs hnd μ f (orbitalPoint X q) ∂ν) =
      ∫ Y, Θ Y * f Y ∂μ.measure
    simp only [pairingFourierSB_apply]
    calc
      _ = ∫ p, k p ∂ν.prod μ.measure := (integral_prod k hi).symm
      _ = ∫ Y, Θ Y * f Y ∂μ.measure := by
        rw [integral_prod_symm k hi]
        congr with Y
        exact integral_mul_const (f Y) _

end Langlands.HarmonicAnalysis.UnitConjugation
