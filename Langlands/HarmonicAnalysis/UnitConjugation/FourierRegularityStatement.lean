import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Harish-Chandra's Theorem 4.4: local summability on the Lie algebra of `Aˣ`

The local summability clause of Harish-Chandra's Theorem 4.4 (Theorem 3 of the original) for the
Lie algebra `A` of the unit group `Aˣ` of a finite-dimensional semisimple algebra over a
nonarchimedean local field `F` of characteristic zero: the Fourier transform of a
conjugation-invariant distribution supported in the closure of the saturation of a compact set
is given by a locally integrable function (`LieAlgebraFourierRegularityStatement`). The statement
is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed pp. 1–2, and Theorem 4.4, printed p. 31,
clause (1) with the local summability of `F`.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation

/-- **Harish-Chandra's Theorem 4.4, local summability clause**, for the unit group of a
finite-dimensional semisimple algebra. For every nonarchimedean local field `F` of
characteristic zero, every finite-dimensional semisimple `F`-algebra `A` with its module
topology and Borel σ-algebra, every nontrivial continuous unitary character `ψ` of `F`, every
symmetric nondegenerate bilinear form `B` on `A` invariant under conjugation by `Aˣ`, every
additive Haar measure `μ` on `A`, every compact `ω ⊆ A` and every conjugation-invariant
distribution `T` on `A` supported in the closure of `⋃_u u ω u⁻¹`, there is a function
`Θ : A → ℂ`, locally integrable for `μ`, with `T̂(f) = ∫ Θ(X) f(X) dμ(X)` for every
Schwartz–Bruhat function `f`, where `T̂(f) = T(f̂)` and `f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)`. -/
def LieAlgebraFourierRegularityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A) (ω : Set A), IsCompact ω →
      ∀ T ∈ invariantSupportedIn ω,
        ∃ Θ : A → ℂ, LocallyIntegrable Θ μ.measure ∧
          ∀ f : SchwartzBruhat A,
            distributionFourier ψ hB.isSymm hB.nondegenerate μ T f =
              ∫ X, Θ X * f X ∂μ.measure

end Langlands.HarmonicAnalysis
