import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Fourier transforms of regular orbital distributions are locally integrable

The local summability part of Harish-Chandra's Theorem 1.1 for the Lie algebra `A` of the unit
group `Aˣ` of a finite-dimensional semisimple algebra over a nonarchimedean local field `F` of
characteristic zero: for a regular element `X ∈ g'`, Haar measures on `Aˣ` and on the centralizer
of `X`, a compatible quotient measure and absolutely convergent orbital integrals, the Fourier
transform of the orbital distribution of `X` is given by a locally integrable function
(`RegularOrbitalFourierRegularityStatement`). The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1, printed p. 5: for a Cartan subalgebra `h`,
`φ_f(H) = |η(H)|^{1/2} ∫_{G/A} f(x.H) dx*` (`H ∈ h'`); Theorem 1.1 (Theorem 8): "The distribution
`f ↦ φ_{f̂}(H₀)` (`f ∈ D`) is a locally summable function on `g` which is locally constant on
`g'`."
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Theorem 1.1, local summability**, for the unit group of a
finite-dimensional semisimple algebra. For every nonarchimedean local field `F` of
characteristic zero, every finite-dimensional semisimple `F`-algebra `A` with its module
topology (Borel σ-algebras on `A` and on `Aˣ`), every nontrivial continuous unitary character
`ψ` of `F`, every invariant pairing `B` on `A`, every additive Haar measure `μ` on `A` and every
regular `X ∈ g'` (`regularSet F A`): for every Haar measure `μG` on `Aˣ`, every bi-invariant
Haar measure `μH` on the centralizer `C` of `X`, every quotient measure `ν` on `C \ Aˣ`
compatible with them, and absolutely convergent orbital integrals
`f ↦ ∫_{C \ Aˣ} f(g⁻¹ X g) dν`, there is a function `Θ : A → ℂ`, locally integrable for `μ`,
with `μ̂_X(f) = ∫ Θ(Y) f(Y) dμ(Y)` for every Schwartz–Bruhat function `f`, where `μ_X` is the
orbital distribution of `X` and `μ̂_X(f) = μ_X(f̂)`. -/
def RegularOrbitalFourierRegularityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A), ∀ X ∈ regularSet F A,
      ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
        [BorelSpace (LeftQuotient (conjugationCentralizer X))]
        (μG : Measure Aˣ) [μG.IsHaarMeasure]
        (μH : Measure (conjugationCentralizer X)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
        (ν : Measure (LeftQuotient (conjugationCentralizer X))),
        IsCompatible (conjugationCentralizer X) μG μH ν →
        ∀ hconv : OrbitalIntegralConverges X ν,
          ∃ Θ : A → ℂ, LocallyIntegrable Θ μ.measure ∧
            ∀ f : SchwartzBruhat A,
              distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution X ν hconv) f =
                ∫ Y, Θ Y * f Y ∂μ.measure

end Langlands.HarmonicAnalysis
