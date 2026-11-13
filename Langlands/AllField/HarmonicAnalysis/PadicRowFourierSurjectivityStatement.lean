import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.AllField.LocalField.Foundation
/-! # Row Fourier surjectivity for every supplied Haar measure

These are proposition targets, not proofs. The main target uses exactly the
supplied field topology and its Borel measurable space, in every dimension.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Every Schwartz--Bruhat cutoff is the plus-sign row Fourier transform of a
Schwartz--Bruhat kernel for the supplied topology and any scalar Haar measure.
No self-dual normalization is assumed, including when `d = 0`. -/
def PadicRowFourierSurjectivityStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) (d : ℕ) : Prop :=
  letI := T.topology
  letI := borel F
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : AdditiveHaarMeasure F)
    (Φ : SchwartzBruhat (Fin d → F)),
    ∃ κ : SchwartzBruhat (Fin d → F), IsRowFourierPair ψ ν κ Φ

end Langlands.AllField.HarmonicAnalysis
