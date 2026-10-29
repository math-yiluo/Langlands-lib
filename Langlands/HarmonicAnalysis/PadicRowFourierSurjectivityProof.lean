import Langlands.HarmonicAnalysis.PadicRowFourierSurjectivityStatement
import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Langlands.HarmonicAnalysis.RowFourierHaarSurjectivityProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-! # Row Fourier surjectivity for every supplied p-adic Haar measure -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u

/-- Every actual row test function has a Fourier preimage for the supplied
p-adic topology and arbitrary scalar Haar measure, in every finite dimension. -/
theorem padicRowFourierSurjectivity {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) (d : ℕ) :
    PadicRowFourierSurjectivityStatement F T d := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.fieldT2
  let := T.secondCountableTopology
  let : BorelSpace (Fin d → F.Carrier) := inferInstance
  obtain ⟨htd, hexists⟩ := padicSelfDualMeasureExists F T
  let := htd
  intro ψ ν Φ
  obtain ⟨μ, hμ⟩ := hexists ψ
  obtain ⟨hclosed, hself⟩ := rowFourierCompatibility ψ μ d hμ
  exact rowFourierHaarSurjectivity ψ μ d hclosed hself ν Φ

end Langlands.HarmonicAnalysis
