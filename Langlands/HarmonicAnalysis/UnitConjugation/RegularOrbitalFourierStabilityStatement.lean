import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier

/-!
# The space `D₀` is stable under the Fourier transform

Harish-Chandra's Lemma 3.16 (first half) for the Lie algebra `A` of the unit group of a
finite-dimensional semisimple algebra over a nonarchimedean local field `F` of characteristic
zero: if all regular orbital integrals of a Schwartz–Bruhat function `f` vanish, so do those of
its Fourier transform `f̂` (`LieAlgebraRegularOrbitalFourierStabilityStatement`). The statement
is not proved here.

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3.5, printed p. 28, Lemma 3.16 (Lemma 8): "Suppose `f ∈ D₀` and
`t ∈ Ω^×`. Then `f̂` and `f_t` are also in `D₀`." The proof there writes `φ_{f̂}(H₀)` as the
integral of `f` against the locally summable function of Theorem 1.1 and applies the Weyl
integration formula.
-/

namespace Langlands.HarmonicAnalysis

open MeasureTheory UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Lemma 3.16, Fourier transforms.** For every nonarchimedean local field `F`
of characteristic zero, every finite-dimensional semisimple `F`-algebra `A` with its module
topology (Borel σ-algebras on `A` and on `Aˣ`), every nontrivial continuous unitary character
`ψ` of `F`, every invariant pairing `B` on `A` and every additive Haar measure `μ` on `A`: if
all regular orbital integrals of a Schwartz–Bruhat function `f` vanish
(`RegularOrbitalVanishing F A f`), then all regular orbital integrals of its Fourier transform
`f̂(Y) = ∫ ψ(B(Y, X)) f(X) dμ(X)` vanish. -/
def LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    [TopologicalSpace A] [IsModuleTopology F A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Aˣ] [BorelSpace Aˣ],
    haveI := IsModuleTopology.isTopologicalRing F A
    ∀ (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
      (μ : AdditiveHaarMeasure A) (f : SchwartzBruhat A),
      RegularOrbitalVanishing F A f →
        RegularOrbitalVanishing F A (pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f)

end Langlands.HarmonicAnalysis
