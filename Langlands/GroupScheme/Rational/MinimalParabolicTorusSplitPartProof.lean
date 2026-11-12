import Langlands.GroupScheme.Rational.MinimalParabolicTorusSplitPartReduction
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusLeviReduction
import Langlands.GroupScheme.Rational.ParabolicGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.ParabolicRadicalTorusInitialLevi
import Langlands.GroupScheme.Rational.ReductiveGeometricSolvableRadicalReduction
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusProof
import Langlands.GroupScheme.Rational.LargestCentralSubtorusBaseChangeProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.MinimalParabolicCompatibleRefinement
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Split parts of maximal tori in minimal rational parabolics: proof -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A dynamic presentation of a minimal rational parabolic makes the split component of any
rational Levi an ambient maximal split torus. Its factor through the specified geometric
solvable radical has the image of that Levi as whole-torus centralizer. -/
theorem minimalParabolicLeviCentralizer_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) :
    MinimalParabolicLeviCentralizerStatement.{u} := by
  intro k _ G hG P j hj L l hl R r hR
  obtain ⟨χ, hχ⟩ := (hPD k G hG P j hj.1.isClosedSubgroup).mp hj.1
  have : IsClosedImmersion j.hom.hom.left := hj.1.isClosedSubgroup
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k L hl.isConnectedReductive).1
  have hmax : IsMaximalSplitTorus (a ≫ l ≫ j) :=
    hl.isMaximalSplitTorus_splitComponent_of_dynamicMinimalParabolic hG hj χ hP ha
  obtain ⟨_, _, _, hcent⟩ := hl.exists_splitComponentCocharacter_of_dynamicParabolic hG χ hP ha
  let aR := hl.centralTorusRadicalFactor a hR.1 ha.1.1.1.isTorus ha.1.1.2 ha.1.2
  have hfac : aR ≫ r = a ≫ l :=
    hl.centralTorusRadicalFactor_comp a hR.1 ha.1.1.1.isTorus ha.1.1.2 ha.1.2
  have hamb : aR ≫ r ≫ j = a ≫ l ≫ j := by
    rw [← Category.assoc, hfac, Category.assoc]
  exact ⟨A, aR, by rw [hamb]; exact hmax, by rw [hamb]; exact hcent⟩

/-- A dynamic description of rational parabolics supplies the adapted rational Levi of a
maximal torus in a parabolic, through the published six-input assembly. -/
theorem parabolicRadicalTorusLevi_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) :
    ParabolicRadicalTorusLeviStatement.{u} :=
  parabolicRadicalTorusLevi_of_structural_inputs
    (parabolicGeometricSolvableRadicalExists_of_structure hPD dynamicCentralizerReductive
      (reductiveGeometricSolvableRadicalExists_of_structure solvableRadicalExistence
        algClosedReductiveNormalSolvableTorus reductiveLargestCentralSubtorusBaseChange))
    maximalRankRadicalTorusIntersection maximalTorusBaseChange
    borelContainingSubgroupConnectedStatement
    (parabolicRadicalTorusCentralizerLevi_of_dynamic hPD dynamicCentralizerReductive
      solvableMaximalTorusConjugacy)
    maximalTorusCentralizer

/-- The dynamic description of rational parabolics implies the minimal-parabolic split-part
statement. -/
theorem minimalParabolicTorusSplitPart_of_parabolicDynamic
    (hPD : ParabolicDynamicStatement.{u}) :
    MinimalParabolicTorusSplitPartStatement.{u} :=
  minimalParabolicTorusSplitPartStatement_of_radical_torus_levi
    (parabolicRadicalTorusLevi_of_parabolicDynamic hPD)
    (minimalParabolicLeviCentralizer_of_parabolicDynamic hPD)

/-- Ambient maximality and centralizers of torus split parts in minimal rational parabolics,
with no premise beyond the published statement's hypotheses. -/
theorem minimalParabolicTorusSplitPart : MinimalParabolicTorusSplitPartStatement.{u} :=
  minimalParabolicTorusSplitPart_of_parabolicDynamic parabolicDynamic

end Langlands.GroupScheme
