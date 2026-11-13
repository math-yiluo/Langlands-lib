import Langlands.HarmonicAnalysis.PadicRowFourierCutoffProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffStatement
/-!
# Simultaneous normalized local-field row Fourier cutoffs: proof

A compact open product subgroup `L = Sᵈ` of rows lies inside the prescribed
neighbourhood of zero, and the character of the row pairing is trivial on
`L × C`. The small cutoff is `κ = vol(L)⁻¹ · 1_L`, and the large cutoff is its
plus-sign row transform. Row inversion and the evenness of `κ` make the pair
`(Φ, κ)` a Fourier pair in the stated direction.
-/

noncomputable section

open MeasureTheory Topology Filter Set

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRowFourierCutoffStatement padicRowFourierCutoff
open Langlands.AllField.HarmonicAnalysis

universe u

section Generic

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [NonarchimedeanAddGroup F] [LocallyCompactSpace F]

variable [T2Space F] [MeasurableSpace F] [BorelSpace F] [TotallyDisconnectedSpace F]

end Generic

/-- Simultaneous normalized row Fourier cutoffs for every supplied topology,
self-dual scalar Haar measure and dimension. -/
theorem padicRowFourierCutoff (F : Type u) [Field F]
    (T : LocalFieldData F) (d : ℕ) : PadicRowFourierCutoffStatement F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : NonarchimedeanAddGroup F := rowFourierCutoff_nonarchimedean
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  intro ψ ν hsd C hC U hU h0
  exact exists_rowFourierCutoff ψ ν hsd hC hU h0

end Langlands.AllField.HarmonicAnalysis
