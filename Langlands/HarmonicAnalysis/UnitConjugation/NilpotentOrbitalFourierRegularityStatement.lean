import Langlands.HarmonicAnalysis.UnitConjugation.FourierRegularityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.OrbitalDistribution

/-!
# Fourier transforms of nilpotent orbital distributions are locally integrable

The specialization of Harish-Chandra's Theorem 4.4 to the orbital distribution of a nilpotent
element `N` of a finite-dimensional semisimple algebra `A` over a nonarchimedean local field of
characteristic zero: for Haar measures on `Aˣ` and on the centralizer of `N`, a compatible
quotient measure and absolutely convergent orbital integrals, the Fourier transform of the
orbital distribution of `N` is given by a locally integrable function
(`NilpotentOrbitalFourierRegularityStatement`). The statement is not proved here.

`LieAlgebraFourierRegularityStatement.nilpotentOrbital` (proved) derives it from
`LieAlgebraFourierRegularityStatement`: the orbital distribution of `N` lies in `J({N})` for the
compact set `{N}`. `distributionFourier_orbitalDistribution_zero` (proved) computes the case
`N = 0` directly: the transform is the constant `ν(C \ Aˣ)` times `μ`.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed pp. 2–3: "It follows from Theorem 4.4
(Theorem 3) that `μ̂_O` is a function." Clozel, *Characters of non-connected, reductive p-adic
groups*, Canad. J. Math. 39 (1987), §3.3, Theorem 3, printed p. 154, uses the Fourier
transforms `ν̂_O` of the invariant measures on the nilpotent orbits as functions.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Fourier transforms of nilpotent orbital distributions are functions.** For every
nonarchimedean local field `F` of characteristic zero, every finite-dimensional semisimple
`F`-algebra `A` with its module topology (Borel σ-algebras on `A` and on `Aˣ`), every nontrivial
continuous unitary character `ψ` of `F`, every invariant pairing `B` on `A`, every additive Haar
measure `μ` on `A` and every nilpotent `N : A`: for every Haar measure `μG` on `Aˣ`, every
bi-invariant Haar measure `μH` on the centralizer `C` of `N`, every quotient measure `ν` on
`C \ Aˣ` compatible with them, and absolutely convergent orbital integrals
`f ↦ ∫_{C \ Aˣ} f(g⁻¹ N g) dν`, there is a function `Θ : A → ℂ`, locally integrable for `μ`,
with `μ̂_N(f) = ∫ Θ(X) f(X) dμ(X)` for every Schwartz–Bruhat function `f`, where `μ_N` is the
orbital distribution of `N` and `μ̂_N(f) = μ_N(f̂)`. -/
def NilpotentOrbitalFourierRegularityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A) (N : A), IsNilpotent N →
      ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer N))]
        [BorelSpace (LeftQuotient (conjugationCentralizer N))]
        (μG : Measure Aˣ) [μG.IsHaarMeasure]
        (μH : Measure (conjugationCentralizer N)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
        (ν : Measure (LeftQuotient (conjugationCentralizer N))),
        IsCompatible (conjugationCentralizer N) μG μH ν →
        ∀ hconv : OrbitalIntegralConverges N ν,
          ∃ Θ : A → ℂ, LocallyIntegrable Θ μ.measure ∧
            ∀ f : SchwartzBruhat A,
              distributionFourier ψ hB.isSymm hB.nondegenerate μ (orbitalDistribution N ν hconv) f =
                ∫ X, Θ X * f X ∂μ.measure

/-- Harish-Chandra's Theorem 4.4 gives the nilpotent orbital statement: the orbital distribution
of `N` for a compatible quotient measure lies in `J({N})`, `{N}` being compact. -/
theorem LieAlgebraFourierRegularityStatement.nilpotentOrbital.{u, v}
    (h : LieAlgebraFourierRegularityStatement.{u, v}) :
    NilpotentOrbitalFourierRegularityStatement.{u, v} := by
  intro F _ _ _ _ _ A _ _ _ _ _ _ _ _ _ _
  have := IsModuleTopology.isTopologicalRing F A
  intro ψ B hB μ N _ _ _ μG _ μH _ _ ν hcompat hconv
  exact h F A ψ B hB μ {N} isCompact_singleton (orbitalDistribution N ν hconv)
    (orbitalDistribution_mem_invariantSupportedIn_of_isCompatible N μG μH ν hcompat hconv)

/-- The orbit of `0`: the Fourier transform of `f ↦ ν(C \ Aˣ) f(0)` is the constant function
`ν(C \ Aˣ)` against `μ`, since `f̂(0) = ∫ f dμ`. -/
theorem distributionFourier_orbitalDistribution_zero.{u, v}
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [TopologicalSpace A]
    [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    (ψ : UnitaryAdditiveCharacter F) {B : LinearMap.BilinForm F A} (hs : B.IsSymm)
    (hnd : B.Nondegenerate) (μ : AdditiveHaarMeasure A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer (0 : A)))]
    (ν : Measure (LeftQuotient (conjugationCentralizer (0 : A))))
    (hconv : OrbitalIntegralConverges (0 : A) ν) (f : SchwartzBruhat A) :
    distributionFourier ψ hs hnd μ (orbitalDistribution (0 : A) ν hconv) f =
      ∫ X, (ν.real Set.univ : ℂ) * f X ∂μ.measure := by
  rw [distributionFourier_apply, orbitalDistribution_zero_apply, pairingFourierSB_apply,
    ← integral_const_mul]
  congr 1
  funext X
  simp
