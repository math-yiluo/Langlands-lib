import Langlands.Correspondence.HenniartCandidateExistenceReductionStatement
import Langlands.Global.Arithmetic.HenniartGlobalizationReduction
import Langlands.Global.Factors.RelativePolePairingProof
import Langlands.ClassField.Global.FundamentalClassProof
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Automorphic.AssociatedCentralCharacterProof
import Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof
import Langlands.ClassField.Global.LocalRelativeWeilTransferProof

/-! # Proof of Henniart's candidate existence from its open global inputs

Proves `Langlands.Henniart.CandidateExistenceReductionStatement`: the five open global inputs
give a candidate at every finite Galois quotient of a p-adic field, at automorphic-lattice
universe `0`.
-/

namespace Langlands.Henniart

universe uK uW uP uE uQ

open Langlands.Global Langlands.ClassField.Global Langlands.Global.PoleComparison

/-- Henniart's candidate existence (universe `0` automorphic lattices) from Harris's
Proposition 4.8, Théorème 2.4, local class formation, the certified pole comparisons and the
composite-map transport. -/
theorem candidateExistenceReduction :
    CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ} := by
  intro hHarris hasi hlcf hpole hcomp p _ K Q _ _ q
  choose I hI using hlcf
  have hI' : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization :=
    fun p _ => ⟨(hI p).2.1, (hI p).1⟩
  obtain ⟨c, hc, -⟩ := globalFundamentalClassStatement.{0}.2 I hI'
  have hcar : RelativeWeilGroup.IsArithmeticClassFamily c := ⟨I, hI', hc⟩
  obtain ⟨F, E, _, _, _, _, _, _, v, h, f, hcov⟩ :=
    henniartGlobalization_of_inputs.{uK, uQ, uW, uP}
      LocalClassField.commonClosureReciprocityExistence
      RelativeWeilGroup.localInducedRestriction
      RelativeWeilGroup.associatedCentralCharacter hasi
      RelativeWeilGroup.localTransferReciprocity hHarris c hcar p K q
  have : CompactSpace (AdeleQuotient F) := compactSpace_adeleQuotient F
  let ψ := HeckeFunctionalEquation.standardFiniteAdditiveComponent F v
  have hpc := hpole F E c hcar v ψ
  obtain ⟨-, -, T, hT, -⟩ := relativePolePairing.{0, uW, uP} F E c hcar v ψ hpc
  refine ⟨_, _, henniartCompositeMap F E c v h K f T, ?_,
    hcomp F E c hcar v ψ hpc T hT p h K f⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcov x hx
  exact ⟨y, hy, (continuousRestrict_completionWeilTransport_eq_iff v h K f y x).mp hxy⟩

end Langlands.Henniart
