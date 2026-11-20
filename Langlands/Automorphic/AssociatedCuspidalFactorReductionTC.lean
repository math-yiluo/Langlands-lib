import Langlands.Automorphic.AssociatedFactorTCReductionStatement
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.LocalFactor.UnitaryArithmeticPair

/-! # Henniart's cuspidal factor reduction over totally complex fields -/

noncomputable section

universe u uV uP uQ uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic

/-- Théorème 2.4 and Corollaire 2.3 imply Corollaire 2.4 over totally complex fields. -/
theorem associatedCuspidalFactorReductionTC :
    AssociatedCuspidalFactorReductionTCStatement.{u, uV, uP, uQ, uE} := by
  intro hInduction hFactor c hc F E _ _ _ _ _ _ _ _ ψ hψ r t S S' T T'
    hSI hSU hSI' hSU' hT hT' hS hS'
    P P' v hI hA hI' hA' w e ι hι ψv hψv
  let := (padicField v).canonicalTopologicalData.topology
  obtain ⟨B, σ, hUnit, ⟨equiv⟩⟩ :=
    hInduction c hc F E S T hSI hSU hT hS P v hI hA
  obtain ⟨B', σ', hUnit', ⟨equiv'⟩⟩ :=
    hInduction c hc F E S' T' hSI' hSU' hT' hS' P' v hI' hA'
  have hTempered :=
    Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct.{u, u, u}
      (padicField v) (Nat.succ_pos r) B σ hUnit
      ((P.localComponent v).padicObject hI hA).obj.representation equiv
  have hTempered' :=
    Classification.isTempered_of_equiv_unitarizableSupercuspidalProduct.{u, u, u}
      (padicField v) (Nat.succ_pos t) B' σ' hUnit'
      ((P'.localComponent v).padicObject hI' hA').obj.representation equiv'
  exact hFactor c hc F E ψ hψ S S' T T' hS hS'
    P P' v hI hA hI' hA' hTempered hTempered' w e ι hι
    (localComponent_isUnitary ι hSU) (localComponent_isUnitary ι hSU') ψv hψv

end Langlands.ClassField.Global.RelativeWeilGroup
