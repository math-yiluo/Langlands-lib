import Langlands.LocalField.Definitions
import Langlands.HarmonicAnalysis.Basic

/-! A focused scalar self-dual Haar existence target for each supplied p-adic topology. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every continuous nontrivial unitary additive character admits a genuine
self-dual additive Haar measure for the supplied p-adic topology.
Total disconnectedness is asserted explicitly as part of the conclusion. -/
def PadicSelfDualMeasureExistsStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  ∃ htd : TotallyDisconnectedSpace F.Carrier,
  letI := htd
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier, SelfDualMeasureExists ψ

end Langlands.HarmonicAnalysis
