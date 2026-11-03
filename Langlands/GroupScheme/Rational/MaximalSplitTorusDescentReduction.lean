import Langlands.GroupScheme.Rational.MaximalSplitTorusDescentStatement
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeStatement
import Langlands.GroupScheme.PseudoParabolicStructureStatement
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicStatement

/-! # Assembly of the two structural descent branches -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Structural assembly reduces the two-branch descent proposition to the
common solvable envelope, pseudo-parabolic structure and rational containment
propositions. This is a conditional implication, with all three prerequisite
propositions explicit. -/
def SmoothMaximalSplitTorusDescentReductionStatement : Prop :=
  NoProperPseudoParabolicSolvableEnvelopeStatement.{u} →
    PseudoParabolicSubgroupStructureStatement.{u} →
      SplitTorusIntoPseudoParabolicStatement.{u} →
        SmoothMaximalSplitTorusDescentStatement.{u}

/-- The common solvable envelope and rational containment in a proper
pseudo-parabolic supply the two branches of closed-subgroup descent. -/
theorem smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment
    (henvelope : NoProperPseudoParabolicSolvableEnvelopeStatement.{u})
    (hstructure : PseudoParabolicSubgroupStructureStatement.{u})
    (hcontainment : SplitTorusIntoPseudoParabolicStatement.{u}) :
    SmoothMaximalSplitTorusDescentStatement.{u} := by
  classical
  intro k _ G _ _ _
  by_cases hproper :
      ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
        IsPseudoParabolicSubgroup i ∧ ¬ IsIso i
  · obtain ⟨P, i, hi, hnotiso⟩ := hproper
    obtain ⟨hsm, hco, haf⟩ := hstructure k G P i hi
    exact Or.inr ⟨P, hsm, haf, hco, i, hi.isClosedSubgroup,
      hnotiso, hcontainment k G P i hi⟩
  · have hnone :
        ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
          IsPseudoParabolicSubgroup i → IsIso i := by
      intro P i hi
      by_contra hnotiso
      exact hproper ⟨P, i, hi, hnotiso⟩
    obtain ⟨H, j, hj, hsm, hco, haf, hsolv, hfactor⟩ :=
      henvelope k G hnone
    exact Or.inl ⟨H, hsm, haf, hco, j, hj, hsolv, hfactor⟩

/-- The conditional structural reduction, as a proposition with its proof. -/
theorem smoothMaximalSplitTorusDescentReduction :
    SmoothMaximalSplitTorusDescentReductionStatement.{u} :=
  smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment

/-- Conditional final assembly from solvable conjugacy and the three
published structural prerequisite propositions. -/
theorem smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment
    (hsolvable : SolvableMaximalSplitTorusConjugacyStatement.{u})
    (henvelope : NoProperPseudoParabolicSolvableEnvelopeStatement.{u})
    (hstructure : PseudoParabolicSubgroupStructureStatement.{u})
    (hcontainment : SplitTorusIntoPseudoParabolicStatement.{u}) :
    SmoothMaximalSplitTorusConjugacyStatement.{u} :=
  smoothMaximalSplitTorusConjugacy_of_solvable_of_descent hsolvable
    (smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment
      henvelope hstructure hcontainment)

end Langlands.GroupScheme
