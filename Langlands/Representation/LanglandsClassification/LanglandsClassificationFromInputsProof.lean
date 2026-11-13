import Langlands.Representation.LanglandsClassification.LanglandsClassificationFromInputsStatement
import Langlands.Representation.LanglandsClassification.LanglandsQuotientUniqueReduction
import Langlands.Representation.LanglandsClassification.LanglandsQuotientMutualRigidityProof
import Langlands.Representation.LanglandsClassification.OppositeJacquetExhaustionReduction
import Langlands.Representation.LanglandsClassification.OppositeJacquetUntwistSelectionReduction
import Langlands.Representation.LanglandsClassification.OppositeStandardExponentRestrictionProof
import Langlands.Representation.LanglandsClassification.OppositeUntwistTemperedCriterion
import Langlands.Representation.LanglandsClassification.LanglandsTripletRegularityProof
import Langlands.Representation.Intertwining.OppositeIdentitySupportProof
import Langlands.GroupScheme.Rational.LanglandsDecompositionProof

/-! # The Langlands classification from its remaining inputs: proof

Proves `LanglandsClassificationFromInputsStatement` (Renard VII.4.2 from second
adjointness, finite length of normalized induction and Jacquet modules, and admissibility
of irreducible representations) by combining the published reductions of parts (i), (ii)
and (iii) with the published proofs of their other inputs.
-/

universe u v

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.4.2 follows from second adjointness, finite length of normalized induction
and of normalized Jacquet modules, and admissibility of irreducible smooth representations. -/
theorem langlandsClassificationFromInputs :
    LanglandsClassificationFromInputsStatement.{u, v} :=
  fun hAdj hFin hIrr hFL =>
    ⟨langlandsQuotientUnique_of_inputs hAdj hFin oppositeIdentitySupport
        langlandsTripletOppositeKernel,
      langlandsQuotientInjective_of_secondAdjointness hAdj,
      langlandsQuotientExhaustive_of_selectedUnitaryUntwist
        (oppositeJacquetUntwistSelection_of_inputs
          Langlands.GroupScheme.langlandsCombinatorialDecomposition hIrr hFL
          oppositeStandardExponentRestriction oppositeUntwistTemperedCriterion) hAdj⟩

end Langlands.Aubert.General.RepresentedParabolic
