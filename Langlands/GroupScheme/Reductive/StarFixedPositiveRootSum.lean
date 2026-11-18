import Langlands.GroupScheme.Reductive.InnerStarWeights
import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Langlands.LinearAlgebra.RootDatumZeroFace

/-! # The positive-root sum as a star-fixed weight -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GaloisPinningData

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : GaloisPinningData k K G) [Fintype d.toSplitPinning.rootIndex]

/-- The published positive-root sum, equipped with its invariance under the full
star action. -/
def starFixedPositiveRootSum : {χ // d.IsStarFixedWeight χ} := by
  classical
  refine ⟨IntegralWeylVector.positiveRootSum d.toSplitPinning.rootDatum d.toSplitPinning.base,
    ?_⟩
  intro σ
  let θ := (d.starAction σ).val
  have hpos (i : d.toSplitPinning.rootIndex) :
      d.toSplitPinning.base.IsPos (θ.indexEquiv i) ↔ d.toSplitPinning.base.IsPos i :=
    LinearAlgebra.RootDatumZeroFace.isPos_indexEquiv_iff_of_based
      d.toSplitPinning.base θ (d.starAction σ).property i
  change θ.weightEquiv (IntegralWeylVector.positiveRootSum
    d.toSplitPinning.rootDatum d.toSplitPinning.base) = _
  rw [IntegralWeylVector.positiveRootSum, map_sum]
  apply Finset.sum_equiv θ.indexEquiv
  · intro i
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hpos i).symm
  · intro i _
    exact θ.root_weightMap_apply d.toSplitPinning.rootDatum d.toSplitPinning.rootDatum i

/-- The sum of the positive roots is fixed by each element of the star action. -/
theorem starAction_positiveRootSum (σ : K ≃ₐ[k] K) :
    (d.starAction σ).val.weightEquiv
        (IntegralWeylVector.positiveRootSum d.toSplitPinning.rootDatum d.toSplitPinning.base) =
      IntegralWeylVector.positiveRootSum d.toSplitPinning.rootDatum d.toSplitPinning.base :=
  d.starFixedPositiveRootSum.property σ

end Langlands.GroupScheme.GaloisPinningData
