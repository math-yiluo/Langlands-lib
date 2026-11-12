import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.ReductivePseudoParabolicComparison
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicConjugacyAssembly
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureReduction
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicCentralizerProduct
import Langlands.GroupScheme.Rational.PseudoParabolicMinimalityCriterionReduction
import Langlands.GroupScheme.Rational.PseudoParabolicSplitSolvableEnvelopeProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Reductive.SplitUnipotentRadicalExistenceProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalProductProof
import Langlands.GroupScheme.PseudoParabolicSplitRadicalContainmentProof

/-! # Rational conjugacy of minimal parabolic subgroups

Borel–Tits, *Groupes réductifs*, Théorème 4.13(b), over every field. The proof
goes through minimal pseudo-parabolic subgroups (Conrad–Gabber–Prasad,
Theorem C.2.5), which coincide with minimal parabolic subgroups of a connected
reductive group. Every structural input is a published proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace MinimalParabolicConjugacyProof

/-- CGP Lemma C.2.2: a split solvable smooth connected subgroup can be conjugated
by a rational point into any pseudo-parabolic subgroup. -/
theorem splitSolvableIntoPseudoParabolic : SplitSolvableIntoPseudoParabolicStatement.{u} :=
  splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
    pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
    splitSolvablePseudoCompleteFixedPoint pseudoParabolicQuotientRationalLifting

/-- CGP Proposition C.2.4 with the maximality observation preceding it. -/
theorem pseudoParabolicMaximalSplitTorusStructure :
    PseudoParabolicMaximalSplitTorusStructureStatement.{u} := by
  intro k _ G P _ _ _ i hi S s hs
  obtain ⟨h1, h2⟩ := pseudoParabolicTorusCentralizerContainment_of_conjugacy
    smoothMaximalSplitTorusConjugacy k G P i hi S s hs
  refine ⟨h1, h2, fun U j hj => ⟨fun hmin => ?_, fun hprod => ?_⟩⟩
  · exact pseudoParabolicCentralizerProductOfMinimality_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitRadicalProduct
      pseudoParabolicSplitRadicalContainment k G P i hi S s hs U j hj hmin
  · exact pseudoParabolicMinimalityOfCentralizerProduct_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitSolvableEnvelope
      splitSolvableIntoPseudoParabolic k G P i hi S s hs U j hj hprod

/-- CGP Theorem C.2.5: minimal pseudo-parabolic subgroups of a smooth connected
affine group are conjugate by a rational point. -/
theorem minimalPseudoParabolicConjugacy : MinimalPseudoParabolicConjugacyStatement.{u} :=
  minimalPseudoParabolicConjugacy_of_structure pseudoParabolicSubgroupStructure
    SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence
    pseudoParabolicSplitSolvableEnvelope splitSolvableIntoPseudoParabolic
    pseudoParabolicMaximalSplitTorusStructure

end MinimalParabolicConjugacyProof

open MinimalParabolicConjugacyProof

/-- Borel–Tits 4.13(b): any two minimal parabolic subgroups of a connected
reductive group over a field are conjugate by a rational point, as actual
subgroup schemes. -/
theorem minimalParabolicConjugacy : MinimalParabolicConjugacyStatement.{u} :=
  minimalParabolicConjugacyStatement_of_pseudoParabolic parabolicDynamic
    (fun _ _ _ hG => hG.hasTrivialUnipotentRadical) minimalPseudoParabolicConjugacy

end Langlands.GroupScheme
