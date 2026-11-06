import Langlands.Representation.CuspidalSupport.CuspidalJacquetProjectionFromSplitting
import Langlands.Representation.Aubert.General.RationalMinimalJacquetArbitraryCarrier

/-!
# Rational finite embedding reduced to literal Levi Jacquet splittings

The source carrier universe is independent of the field and group universe.
The only additional input is the explicitly stated splitting condition.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The still-required literal splitting input, at exactly the structural
premises and independent universes of the rational finite embedding target. -/
def RationalLeviJacquetCuspidalRemainderSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      LeviJacquetCuspidalRemainderSplittingTarget.{u, u, v}
        (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU hM
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

/-- The explicit literal Levi splitting condition suffices for the unchanged
closed rational finite embedding target. No splitting existence is asserted. -/
theorem rationalCuspidalInducedEmbedding_of_leviJacquetSplittings
    (hsplit : RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, v}) :
    RationalCuspidalInducedEmbeddingStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  apply finiteCuspidalInducedEmbedding_of_splittings
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν) hU hM
    (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
  · exact fun I =>
      standardUnipotent_isUnimodular_of_standardCocharacterStatement
        i ν hStandard hG hi hν I (hU I)
  · exact fun I =>
      standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν I
  · intro B hB
    let := hB
    exact exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier
      i ν hStandard hInter hRoots hG hi hν hU hM B
  · exact hsplit k G hG T i hi ν hν hStandard hInter hRoots hU hM

end Langlands.Aubert.General.RationalPointFamily
