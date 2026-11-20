import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Shimura.Unitary.FiniteModels
import Mathlib.Algebra.Ring.Fin
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # The two actual CM places of a split finite center -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped FiniteExtension

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  {p : Langlands.Global.FinitePlace E}

/-- The two factors of a split center identify the actual places above `p`. -/
def SplitPlaceIdentification.placesEquivFinTwo (h : SplitPlaceIdentification E K p) :
    FinitePlacesAbove K p ≃ Fin 2 := by
  let completions := fun q : FinitePlacesAbove K p => FiniteCompletion K q.val
  let splitFactors := fun _ : Fin 2 => FiniteCompletion E p
  let e := AlgEquiv.ofBijective (finiteTensorMap (L := K) p)
    ((completedTensorComparison E K).1 p)
  let f : (∀ q, completions q) ≃+* (∀ i, splitFactors i) :=
    e.symm.toRingEquiv.trans (h.equiv.toRingEquiv.trans (RingEquiv.piFinTwo splitFactors).symm)
  calc
    FinitePlacesAbove K p ≃ (Σ q, PrimeSpectrum (completions q)) :=
      (Equiv.sigmaUnique _ _).symm
    _ ≃ PrimeSpectrum (∀ q, completions q) := (PrimeSpectrum.sigmaToPiHomeo completions).toEquiv
    _ ≃ PrimeSpectrum (∀ i, splitFactors i) := (PrimeSpectrum.comapEquiv f).toEquiv
    _ ≃ (Σ i, PrimeSpectrum (splitFactors i)) :=
      (PrimeSpectrum.sigmaToPiHomeo splitFactors).toEquiv.symm
    _ ≃ Fin 2 := Equiv.sigmaUnique _ _

/-- A split finite place has exactly two actual places above it in the CM field. -/
theorem card_finitePlacesAbove_of_isSplitPlace (h : IsSplitPlace E K p) :
    Fintype.card (FinitePlacesAbove K p) = 2 := by
  obtain ⟨h⟩ := h
  exact (Fintype.card_congr h.placesEquivFinTwo).trans (Fintype.card_fin 2)

end Langlands.Shimura.FiniteUnitary
