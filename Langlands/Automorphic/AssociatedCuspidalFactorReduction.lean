import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.LocalFactor.UnitaryArithmeticPair

/-! # Reduction of Henniart's cuspidal factor comparison

Theorem 2.4 and Corollary 2.3 imply Corollary 2.4, using the published
canonical temperedness bridge and restriction of unitary Weil actions.
The two global inputs are explicit premises of this reduction.
-/

noncomputable section

universe u uV uP uQ uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic

/-- The exact five-universe implication from Henniart's local induction
theorem and tempered factor comparison to his cuspidal factor comparison. -/
def AssociatedCuspidalFactorReductionStatement : Prop :=
  AssociatedSupercuspidalInductionStatement.{u, uV, uP, uQ} →
    AssociatedTemperedFactorStatement.{u, uV, uP, uQ, uE} →
      AssociatedCuspidalFactorStatement.{u, uV, uP, uQ, uE}

/-- Derive the unchanged cuspidal factor statement from the two global inputs.
This is a conditional reduction, rather than a proof of either input. -/
theorem associatedCuspidalFactor_of_supercuspidalInduction_of_tempered
    (hind : AssociatedSupercuspidalInductionStatement.{u, uV, uP, uQ})
    (hfactor : AssociatedTemperedFactorStatement.{u, uV, uP, uQ, uE}) :
    AssociatedCuspidalFactorStatement.{u, uV, uP, uQ, uE} := by
  intro c hc F E _ _ _ _ _ _ _ ψ hψ r t S S' T T'
    hSI hSU hSI' hSU' hT hT' hS hS'
    P P' v hI hA hI' hA' w e ι hι ψv hψv
  have ht :
      letI := (padicField v).canonicalTopologicalData.topology
      PadicField.TopologicalData.IsTempered (padicField v).canonicalTopologicalData
        ((P.localComponent v).padicObject hI hA).obj.representation := by
    let := (padicField v).canonicalTopologicalData.topology
    obtain ⟨B, σ, hu, ⟨eπ⟩⟩ :=
      hind c hc F E S T hSI hSU hT hS P v hI hA
    exact Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct.{u, u, u}
      (padicField v) (Nat.succ_pos r) B σ hu
      ((P.localComponent v).padicObject hI hA).obj.representation eπ
  have ht' :
      letI := (padicField v).canonicalTopologicalData.topology
      PadicField.TopologicalData.IsTempered (padicField v).canonicalTopologicalData
        ((P'.localComponent v).padicObject hI' hA').obj.representation := by
    let := (padicField v).canonicalTopologicalData.topology
    obtain ⟨B, σ, hu, ⟨eπ⟩⟩ :=
      hind c hc F E S' T' hSI' hSU' hT' hS' P' v hI' hA'
    exact Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct.{u, u, u}
      (padicField v) (Nat.succ_pos t) B σ hu
      ((P'.localComponent v).padicObject hI' hA').obj.representation eπ
  exact hfactor c hc F E ψ hψ S S' T T' hS hS'
    P P' v hI hA hI' hA' ht ht' w e ι hι
    (localComponent_isUnitary ι hSU) (localComponent_isUnitary ι hSU') ψv hψv

/-- The packaged global reduction, at five independent universe levels. -/
theorem associatedCuspidalFactorReduction :
    AssociatedCuspidalFactorReductionStatement.{u, uV, uP, uQ, uE} :=
  associatedCuspidalFactor_of_supercuspidalInduction_of_tempered

end Langlands.ClassField.Global.RelativeWeilGroup
