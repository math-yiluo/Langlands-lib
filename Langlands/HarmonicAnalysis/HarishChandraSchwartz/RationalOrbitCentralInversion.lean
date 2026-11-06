import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFourierInversion
import Langlands.Representation.Plancherel.DiscreteSeriesCentralCharacter

/-! # Fourier inversion over `A_G` on a discrete-series orbit with the actual central characters

`RationalOrbitFourierInversion` proves the Fourier inversion step of Proposition VII.2.1
(case `M = G`, printed pp. 317–318) for a function `cc` on the orbit `O` standing for
`ω ↦ χ_ω`, the restriction to `A_G` of the central character, under the twist law
`cc(χ ω₀) = χ|_{A_G} · cc(ω₀)` as a hypothesis. Here `cc` is the actual restriction
`discreteSeriesCentralRestriction` of the central character of each class (Worker 200), whose
twist law `discreteSeriesCentralRestriction_orbitMap` discharges that hypothesis.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.HarishChandraSchwartz

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitCentralInversion1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitCentralInversion2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

/-- `χ_ω` on `A_G`: the restriction to `A_G = s(T(F))` of the actual unitary central character
of the class of `ω ∈ O`. -/
def rationalOrbitCentralCharacter :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega →
          (GroupScheme.rationalPoints.map s).range →* Circle := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega ω
  exact discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center ω.val

omit [IsAffine T.X.left] in
/-- The twist law `χ_{χ ω₀} = χ|_{A_G} · χ_{ω₀}`, in the form of the hypothesis `hcc` of
`RationalOrbitFourierInversion`. -/
theorem rationalOrbitCentralCharacter_orbitMap :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (χ : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
      (a : (GroupScheme.rationalPoints.map s).range),
      ((rationalOrbitCentralCharacter s hs mu omega
          (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ) a :
              Circle) : ℂ) =
        ((χ.val (a : GroupScheme.rationalPoints G) : ℂˣ) : ℂ) *
          (discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
              omega a : ℂ) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega χ a
  change (discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
      (discreteSeriesOrbitMap (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega χ).val a :
          ℂ) = _
  rw [discreteSeriesCentralRestriction_orbitMap, Circle.coe_mul,
    unitaryUnramifiedCircleCharacter_coe]

/-- **Vanishing** with the actual central characters: if `η` differs from `χ_{ω₀}` at a point
of `A_G ∩ G¹`, then `∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = 0`. -/
theorem integral_rationalOrbitCentralInversion_eq_zero
    (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      (∃ b : (GroupScheme.rationalPoints.map s).range,
        (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G ∧
          eta b ≠ discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
              omega b) →
      ∀ {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      ∫ a, rationalOrbitInversionIntegrand s hs mu hindex omega
        (rationalOrbitCentralCharacter s hs mu omega) eta Φ a ∂ν = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ ν _ eta h Φ hΦ
  exact integral_rationalOrbitInversionIntegrand_eq_zero s hs mu hindex hG omega ν
    (rationalOrbitCentralCharacter s hs mu omega) _ eta
    (rationalOrbitCentralCharacter_orbitMap s hs mu omega) h hΦ

/-- **Fourier inversion over `A_G` with the actual central characters**: if `η = χ_{ω₀}` on
`A_G ∩ G¹`, `Φ` is continuous on `O` and the integrand is integrable, then
`∫_{A_G} η(a⁻¹) ∫_O Φ(ω) χ_ω(a) dω dν(a) = ν(A_G ∩ G¹) ∑_{ω ∈ O ; χ_ω = η} Φ(ω)`. -/
theorem integral_rationalOrbitCentralInversion (hG : GroupScheme.IsConnectedReductive G) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
      [BorelSpace (GroupScheme.rationalPoints.map s).range]
      (ν : Measure (GroupScheme.rationalPoints.map s).range) [ν.IsMulLeftInvariant]
      (eta : (GroupScheme.rationalPoints.map s).range →* Circle),
      (∀ b : (GroupScheme.rationalPoints.map s).range,
        (b : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G →
          eta b = discreteSeriesCentralRestriction (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu (GroupScheme.rationalPoints.map s).range hs.range_le_center
              omega b) →
      ∀ {Φ : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega → ℂ}, Continuous Φ →
      Integrable (rationalOrbitInversionIntegrand s hs mu hindex omega
        (rationalOrbitCentralCharacter s hs mu omega) eta Φ) ν →
      ∫ a, rationalOrbitInversionIntegrand s hs mu hindex omega
          (rationalOrbitCentralCharacter s hs mu omega) eta Φ a ∂ν =
        ((ν (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
          ∑ᶠ ω ∈ {ω | rationalOrbitCentralCharacter s hs mu omega ω = eta}, Φ ω := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega _ _ ν _ eta h Φ hΦ hint
  exact integral_rationalOrbitInversionIntegrand s hs mu hindex hG omega ν
    (rationalOrbitCentralCharacter s hs mu omega) _ eta
    (rationalOrbitCentralCharacter_orbitMap s hs mu omega) h hΦ hint

end Langlands.HarishChandraSchwartz
