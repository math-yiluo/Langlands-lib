import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.RowFourier

/-! # Row Fourier surjectivity for every supplied p-adic Haar measure

These are proposition targets, not proofs. The main target uses exactly the
supplied field topology and its Borel measurable space, in every dimension.
-/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every Schwartz--Bruhat cutoff is the plus-sign row Fourier transform of a
Schwartz--Bruhat kernel for the supplied topology and any scalar Haar measure.
No self-dual normalization is assumed, including when `d = 0`. -/
def PadicRowFourierSurjectivityStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) (d : ℕ) : Prop :=
  letI := T.topology
  letI := borel F.Carrier
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : AdditiveHaarMeasure F.Carrier)
    (Φ : SchwartzBruhat (Fin d → F.Carrier)),
    ∃ κ : SchwartzBruhat (Fin d → F.Carrier), IsRowFourierPair ψ ν κ Φ

/-- Conditional transport of row Fourier surjectivity from a scalar Haar
measure whose row transform is closed and self-dual. Regularity is bundled
in `AdditiveHaarMeasure`; the topological hypotheses are explicit. -/
def RowFourierHaarSurjectivityStatement
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
    [SecondCountableTopology K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (d : ℕ) : Prop :=
  RowFourierClosed ψ μ d → IsRowSelfDual ψ μ d →
    ∀ (ν : AdditiveHaarMeasure K) (Φ : SchwartzBruhat (Fin d → K)),
      ∃ κ : SchwartzBruhat (Fin d → K), IsRowFourierPair ψ ν κ Φ

end Langlands.HarmonicAnalysis
