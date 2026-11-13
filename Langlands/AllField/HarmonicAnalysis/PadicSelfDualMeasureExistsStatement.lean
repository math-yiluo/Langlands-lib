import Langlands.HarmonicAnalysis.PadicSelfDualMeasureExistsStatement
import Langlands.AllField.LocalField.Foundation
/-! A focused scalar self-dual Haar existence target for each supplied local-field topology. -/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Every continuous nontrivial unitary additive character admits a genuine
self-dual additive Haar measure for the supplied local-field topology.
Total disconnectedness is asserted explicitly as part of the conclusion. -/
def PadicSelfDualMeasureExistsStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  ∃ htd : TotallyDisconnectedSpace F,
  letI := htd
  ∀ ψ : UnitaryAdditiveCharacter F, SelfDualMeasureExists ψ

end Langlands.AllField.HarmonicAnalysis
