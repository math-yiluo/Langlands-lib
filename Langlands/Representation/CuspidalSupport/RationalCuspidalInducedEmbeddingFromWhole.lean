import Langlands.Representation.CuspidalSupport.RationalFiniteCuspidalEmbeddingReduction
import Langlands.Representation.CuspidalSupport.RationalLeviSplittingFromWhole
import Langlands.GroupScheme.Rational.CentralizerRootSystemInheritance

/-!
# The finite induced-cuspidal embedding from the whole-category splitting

The VI.3.5 whole-category statement is the only remaining input. The Levi
root systems, Levi reductivity and every structural transport are discharged.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The closed whole-category statement gives the literal Levi splitting of
every actual standard Jacquet module, at the same universes. -/
theorem rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, v}) :
    RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro A I
  have hL : IsConnectedReductive (Standard.leviScheme i ν (rootSet i ν I)) :=
    standardLeviScheme_isConnectedReductive i ν hStandard dynamicCentralizerReductive
      hG hi hν I
  exact hasLeviCuspidalRemainderSplitting_of_wholeStatement hwhole G hG T i hi ν
    hStandard hInter hν hU I (hM I)
    (HasRelativeRootSystem.of_standardLeviTorusFactor hRoots hStandard hG hi ν hν
      (rootSet i ν I) (rootSet_subset i ν I) hL (Standard.leviHom i ν (rootSet i ν I))
      (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I))
      (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I)))
    ((jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)).obj A)

/-- The finite induced-cuspidal embedding follows from the closed VI.3.5
whole-category statement at the same independent universes. -/
theorem rationalCuspidalInducedEmbedding_of_wholeStatement
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, v}) :
    RationalCuspidalInducedEmbeddingStatement.{u, v} :=
  rationalCuspidalInducedEmbedding_of_leviJacquetSplittings
    (rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement hwhole)

set_option linter.defProp false in
/-- The reduction of the finite induced-cuspidal embedding to the VI.3.5
whole-category statement, as a declaration whose type is the implication. -/
def rationalCuspidalInducedEmbeddingOfWholeStatement :
    CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, v} →
      RationalCuspidalInducedEmbeddingStatement.{u, v} :=
  rationalCuspidalInducedEmbedding_of_wholeStatement

end Langlands.Aubert.General.RationalPointFamily
