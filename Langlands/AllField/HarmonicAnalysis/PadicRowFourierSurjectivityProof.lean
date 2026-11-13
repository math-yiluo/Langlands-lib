import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
/-! # Row Fourier surjectivity for every supplied Haar measure -/

noncomputable section

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicLatticeHaarStatement PadicLatticeSchwartzExpansionStatement PadicRectangularHaarScalingStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeFourier padicLatticeGeometry padicLatticeHaar padicLatticeSchwartzExpansion padicRowFourierSurjectivity padicScalarHaarScaling padicSchwartzBruhat_exists_additiveLattice_invariant padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Every actual row test function has a Fourier preimage for the supplied
local-field topology and arbitrary scalar Haar measure, in every finite dimension. -/
theorem padicRowFourierSurjectivity 
    (F : Type u) [Field F] (T : LocalFieldData F) (d : ℕ) :
    PadicRowFourierSurjectivityStatement F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := T.fieldT2
  let := T.secondCountableTopology
  let : BorelSpace (Fin d → F) := inferInstance
  obtain ⟨htd, hexists⟩ := padicSelfDualMeasureExists F T
  let := htd
  intro ψ ν Φ
  obtain ⟨μ, hμ⟩ := hexists ψ
  obtain ⟨hclosed, hself⟩ := rowFourierCompatibility ψ μ d hμ
  exact rowFourierHaarSurjectivity ψ μ d hclosed hself ν Φ

end Langlands.AllField.HarmonicAnalysis
