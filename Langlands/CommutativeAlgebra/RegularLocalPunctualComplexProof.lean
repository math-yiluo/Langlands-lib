import Langlands.CommutativeAlgebra.PunctualComplexReduction
import Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityProof
import Langlands.CommutativeAlgebra.RegularLocalKoszulComparison
import Langlands.CommutativeAlgebra.FiniteFreeReversedDualHomotopy

/-! # The punctual perfect complex lemma over a regular local ring -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

namespace Langlands.CommutativeAlgebra

/-- Acyclicity and the Koszul comparison give top reversed-dual homology
of any finite free residue-field resolution. -/
theorem regularLocalResidueResolutionDuality_of_acyclicity
    (hacyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u}) :
    RegularLocalResidueResolutionDualityStatement.{u} := by
  intro R _ _ g hdim C hC _ _ hvan he
  obtain ⟨e⟩ := he
  let comparison := regularLocalKoszulResolutionComparison hacyclicity g hdim C hC hvan e
  exact ⟨(reversedDualHomologyIsoOfHomotopyEquiv (g : ℤ) comparison (g : ℤ)).symm ≪≫
    finiteKoszulCochainReversedDualTopHomologyIsoResidueField _
      (regularLocalParameters_span R g hdim)⟩

/-- The punctual perfect complex statement, with exactly its published
arbitrary-universe type and no additional hypotheses. -/
theorem regularLocalPunctualComplex : RegularLocalPunctualComplexStatement.{u} :=
  regularLocalPunctualComplex_of_acyclicity_of_residueResolutionDuality
    regularLocalFiniteLengthAcyclicity
    (regularLocalResidueResolutionDuality_of_acyclicity regularLocalFiniteLengthAcyclicity)

end Langlands.CommutativeAlgebra
