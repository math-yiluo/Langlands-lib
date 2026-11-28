import Langlands.HarmonicAnalysis.UnitConjugation.EllipticElement
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The elliptic case of Harish-Chandra's Theorem 1.1

The local summability part of Harish-Chandra's Theorem 1.1 for the regular elements that are
elliptic, on the Lie algebra `A` of the unit group `Aˣ` of a finite-dimensional semisimple
algebra over a nonarchimedean local field `F` of characteristic zero
(`EllipticRegularOrbitalFourierRegularityStatement`): for a regular element `X ∈ g'`
(`regularSet F A`) that is elliptic (`IsEllipticElement X`), Haar measures on `Aˣ` and on the
centralizer of `X`, a compatible quotient measure and absolutely convergent orbital integrals,
the Fourier transform of the orbital distribution of `X` is given by a locally integrable
function. The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1: §1.4, printed p. 11, reduces Theorem 1.1 to elliptic Cartan
subalgebras ("So in order to complete the proof of Theorem 1.1 we may assume that `h` is
elliptic"); §§1.5–1.6, printed pp. 11–13 (Lemmas 1.15, 1.17, 1.19, Corollary 1.16 and
Theorem 1.18) prove the elliptic case.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Theorem 1.1, local summability, elliptic case**, for the unit group of a
finite-dimensional semisimple algebra. The hypotheses and the conclusion are those of
`RegularOrbitalFourierRegularityStatement`, with the regular element `X` also elliptic: every
idempotent of `A` commuting with `X` is central (`IsEllipticElement X`), that is the split
component of the centralizer of `X` in `Aˣ` lies in the centre of `Aˣ`. -/
def EllipticRegularOrbitalFourierRegularityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A), ∀ X ∈ regularSet F A, IsEllipticElement X →
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
