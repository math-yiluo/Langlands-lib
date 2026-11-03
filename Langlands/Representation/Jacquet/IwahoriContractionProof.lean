import Langlands.Representation.Jacquet.IwahoriContractionStatements
import Langlands.Representation.Jacquet.IwahoriContractionAdmissibility
import Langlands.Representation.Aubert.General.JacquetAdmissibility

/-! Proof of the conditional Jacquet-lemma and admissibility propositions. -/

namespace Langlands.Jacquet

universe uG uV

/-- The conditional weak Jacquet lemma, its generalized kernel/stable-image
refinement, and the unnormalized and normalized admissibility corollaries. -/
theorem iwahoriContractionJacquet : IwahoriContractionJacquetStatement.{uG, uV} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro G _ _ _ V _ _ ρ hρ K hK N M Nbar g h hMN hfin
    exact fixedJacquetMap_surjective_of_iwahoriContraction ρ hρ hK h hMN hfin
  · intro G _ _ _ V _ _ ρ hρ K hK N M Nbar g h hMN
    exact powerKernelSup_eq_ker_of_iwahoriContraction ρ hρ hK h hMN
  · intro G _ _ _ V _ _ ρ hρ K hK N M Nbar g h hMN hfin
    exact stableImageJacquetMap_bijective_of_iwahoriContraction ρ hρ hK h hMN hfin
  · intro G _ _ _ V _ _ ρ N M Nbar hMN hbasis hadm
    exact isAdmissible_action_of_iwahoriContraction ρ hadm N M Nbar hMN hbasis
  · intro G _ _ _ _ N M Nbar hN hMN hbasis A hA
    exact Aubert.General.isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction
      N M Nbar hN hMN hbasis A hA

end Langlands.Jacquet
