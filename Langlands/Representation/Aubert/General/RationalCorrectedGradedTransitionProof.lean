import Langlands.Representation.Aubert.General.RationalCorrectedGradedReduction
import Langlands.Representation.Aubert.General.RationalCorrectedSupportAssembly
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitRadicalProof
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusTarget
import Langlands.BruhatTits.Parabolic.QuotientCompactProof
import Langlands.GroupScheme.Rational.StandardParabolicPointsProof
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusProof

/-! # The actual surviving graded transitions of the corrected Aubert complex -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The structural inputs of the rational graded reduction, from the standard
parabolics on rational points and the squared intersection modulus. -/
theorem rationalCorrectedGradedTransitionInputs_of_points_of_squaredModulus
    (hPoints : StandardParabolicPointsStatement.{u})
    (hmod : RationalCorrectedOrbitSquaredModulusStatement.{u}) :
    RationalCorrectedGradedTransitionInputs.{u} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ _
  let : DecidableEq (Weyl i) := Classical.decEq _
  intro CM cs hlen hpos hlevi
  refine ⟨fun J => compactSpace_leftQuotient_parabolic i ν
      BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν J,
    rationalCorrectedSurvivingSupportStatement_of_prerequisites
      ⟨hPoints, BruhatTits.dynamicParabolicQuotientCompact⟩
      k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM cs
      hlen hpos hlevi, ?_⟩
  intro I n hn m hm K hK
  obtain ⟨hS1, hS2⟩ := rationalCorrectedOrbitRadicalIntersectionStatement
    k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc CM cs
    hlen hpos hlevi I n hn m hm K hK
  exact ⟨hS1, hS2, hmod k G hG T i hi ν hν hStandard hOrder hInter hRoots hN hZ hU hM hUc
    CM cs hlen hpos hlevi I n hn m hm K hK⟩

/-- **The actual surviving graded transition maps** of the corrected Aubert
complex: the exact Library statement `RationalCorrectedGradedTransitionStatement`. -/
theorem rationalCorrectedGradedTransitionStatement :
    RationalCorrectedGradedTransitionStatement.{u, v} :=
  rationalCorrectedGradedTransitionStatement_of_inputs
    (rationalCorrectedGradedTransitionInputs_of_points_of_squaredModulus
      standardParabolicPointsStatement_proof rationalCorrectedOrbitSquaredModulus)

end Langlands.Aubert.General.RationalPointFamily
