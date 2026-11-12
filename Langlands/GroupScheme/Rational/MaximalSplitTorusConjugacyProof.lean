import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.ConjugacyStatement
import Langlands.GroupScheme.Rational.SplitRankReduction
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.MaximalSplitTorusDescentReduction
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.NoProperPseudoParabolicSolvableEnvelopeProof
import Langlands.GroupScheme.PseudoParabolicStructureProof
import Langlands.GroupScheme.SplitTorusIntoPseudoParabolicReduction
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.PseudoParabolicQuotientPseudoCompleteAssembly
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.PseudoParabolicQuotientRationalLiftingProof

/-! # Rational conjugacy and the rank of maximal split tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Borel–Tits 4.21 and 4.23.** Over every field, maximal split tori of a connected
reductive group are conjugate by a rational point, and every finite splitting of a
maximal split torus has cardinality equal to the split rank. -/
theorem maximalSplitTorusConjugacy : MaximalSplitTorusConjugacyStatement.{u} := by
  apply maximalSplitTorusConjugacyStatement_of_extension_conjugacy
  · intro k _ G hG J _ j hj
    have := hG.isAffineHom
    have := hG.smooth
    exact exists_maximalSplitTorus_extension
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J)
      G j ⟨isSplitTorus_splitTorus J, hj⟩
  · intro k _ G hG
    have := hG.smooth
    have := hG.isAffineHom
    have := hG.connectedSpace
    exact smoothMaximalSplitTorusConjugacy k G

end Langlands.GroupScheme
