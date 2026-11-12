import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicCentralizerProduct
import Langlands.GroupScheme.Rational.PseudoParabolicMinimalityCriterionReduction
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentProof

/-! # Borel–Tits conjugacy of minimal pseudo-parabolic subgroups

The published C.2.5 assembly is instantiated with published proofs. Its two
inputs without a published proof, CGP Lemma C.2.2 and Proposition C.2.4, are
derived here from their published reductions and published proofs, including
CGP Lemma C.2.1 and Theorem C.2.3.
-/

noncomputable section

universe u

namespace Langlands.GroupScheme

namespace MinimalPseudoParabolicConjugacyProof

/-- CGP Lemma C.2.2: a split solvable smooth connected closed subgroup can be
conjugated by a rational point into any pseudo-parabolic subgroup. -/
theorem splitSolvableIntoPseudoParabolic : SplitSolvableIntoPseudoParabolicStatement.{u} :=
  splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
    pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
    splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting

/-- CGP Proposition C.2.4, with the maximality observation preceding it. -/
theorem pseudoParabolicMaximalSplitTorusStructure :
    PseudoParabolicMaximalSplitTorusStructureStatement.{u} := by
  intro k _ G P _ _ _ i hi S s hs
  obtain ⟨hmax, hcentralizer⟩ := pseudoParabolicTorusCentralizerContainment_of_conjugacy
    smoothMaximalSplitTorusConjugacy k G P i hi S s hs
  refine ⟨hmax, hcentralizer, fun U j hj => ⟨fun hmin => ?_, fun hprod => ?_⟩⟩
  · exact pseudoParabolicCentralizerProductOfMinimality_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitRadicalProduct
      pseudoParabolicSplitRadicalContainment k G P i hi S s hs U j hj hmin
  · exact pseudoParabolicMinimalityOfCentralizerProduct_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitSolvableEnvelope
      splitSolvableIntoPseudoParabolic k G P i hi S s hs U j hj hprod

end MinimalPseudoParabolicConjugacyProof

open MinimalPseudoParabolicConjugacyProof

/-- **CGP Theorem C.2.5.** Over every field, any two minimal pseudo-parabolic
subgroups of a smooth connected affine group are conjugate by a rational point. -/
theorem minimalPseudoParabolicConjugacy : MinimalPseudoParabolicConjugacyStatement.{u} :=
  minimalPseudoParabolicConjugacy_of_structure pseudoParabolicSubgroupStructure
    SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence
    pseudoParabolicSplitSolvableEnvelope splitSolvableIntoPseudoParabolic
    pseudoParabolicMaximalSplitTorusStructure

end Langlands.GroupScheme
