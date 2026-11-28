import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Langlands.HarmonicAnalysis.UnitConjugation.RegularSet
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Parabolic descent for Harish-Chandra's Theorem 1.1

For an element `X` of a finite-dimensional algebra `A` over a nonarchimedean local field `F`,
`OrbitalFourierRegularityAt F A X` is the conclusion of Harish-Chandra's Theorem 1.1 (local
summability) at `X`: for every choice of the module topology, Borel σ-algebras, character,
invariant pairing, additive Haar measure, Haar measures on `Aˣ` and on the centralizer of `X`,
compatible quotient measure and convergent orbital integrals, the Fourier transform of the
orbital distribution of `X` is given by a locally integrable function.

`RegularOrbitalFourierDescentStatement` is the parabolic descent of Theorem 1.1, for the unit
group of a finite-dimensional semisimple algebra over a nonarchimedean local field of
characteristic zero: for an idempotent `e` and a regular element `X ∈ g'` commuting with `e`,
if the conclusion holds at `X` for the centralizer `M` of `e` (the Levi subalgebra
`e A e ⊕ (1 - e) A (1 - e)`), then it holds at `X` for `A`. The statement is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §1: §1.2 (parabolic descent, Lemmas 1.4–1.7), printed pp. 6–8,
§1.4 (Lemmas 1.12 and 1.13), printed pp. 9–10, and the reduction to the elliptic case,
printed pp. 10–11.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- The conclusion of Harish-Chandra's Theorem 1.1 (local summability) at an element `X` of a
finite-dimensional algebra `A` over a nonarchimedean local field `F`: for every module topology
on `A` with Borel σ-algebras on `A` and `Aˣ`, every nontrivial continuous unitary character `ψ`
of `F`, every invariant pairing `B`, every additive Haar measure `μ`, every Borel σ-algebra on
the coset space `C \ Aˣ` of the centralizer `C` of `X`, every Haar measure `μG` on `Aˣ`, every
right-invariant Haar measure `μH` on `C`, every compatible quotient measure `ν` and every
proof of absolute convergence of the orbital integrals, there is `Θ : A → ℂ`, locally
integrable for `μ`, with `μ̂_X(f) = ∫ Θ(Y) f(Y) dμ(Y)` for every Schwartz–Bruhat `f`. -/
def OrbitalFourierRegularityAt.{u, v} (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (A : Type v) [Ring A] [Algebra F A]
    [FiniteDimensional F A] (X : A) : Prop :=
  ∀ [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A),
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

/-- **Parabolic descent for Harish-Chandra's Theorem 1.1.** Let `A` be a finite-dimensional
semisimple algebra over a nonarchimedean local field `F` of characteristic zero, `e ∈ A` an
idempotent, `M` the centralizer of `e` in `A` (`Subalgebra.centralizer F {e}`) and `X ∈ M` an
element that is regular in `A`. If the conclusion of Theorem 1.1 holds at `X` for the algebra
`M` (`OrbitalFourierRegularityAt F M X`), it holds at `X` for `A`. -/
def RegularOrbitalFourierDescentStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    (e : A), IsIdempotentElem e →
    ∀ X : Subalgebra.centralizer F ({e} : Set A), (X : A) ∈ regularSet F A →
      OrbitalFourierRegularityAt F (Subalgebra.centralizer F ({e} : Set A)) X →
        OrbitalFourierRegularityAt F A (X : A)

end Langlands.HarmonicAnalysis
