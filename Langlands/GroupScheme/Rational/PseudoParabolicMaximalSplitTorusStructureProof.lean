import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureStatement
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicCentralizerProduct
import Langlands.GroupScheme.Rational.PseudoParabolicMinimalityCriterionReduction
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof

/-! # Maximal split tori and the minimality criterion for pseudo-parabolics

The three published conditional reductions of CGP Proposition C.2.4 are instantiated
with published proofs: Theorem C.2.3, Proposition 2.2.4, the containment part of
Corollary 2.2.5, the split solvable envelope `S ⋉ R_us,k(P)`, and Lemma C.2.2 assembled
from its published components and Lemma C.2.1.
-/

universe u

namespace Langlands.GroupScheme

/-- **CGP Proposition C.2.4**, with the maximality observation preceding it. Over every
field, a maximal split torus `S` of a pseudo-parabolic subgroup `P` of a smooth connected
affine group `G` is maximal split in `G`, satisfies `Z_G(S) ⊆ P` on every relative test,
and `P` is minimal if and only if it represents the fppf-local product of `Z_G(S)` and
any supplied split unipotent radical of `P`. -/
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
      (splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
        pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
        splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting)
      k G P i hi S s hs U j hj hprod

end Langlands.GroupScheme
