import Langlands.GroupScheme.IntegralLinearEmbedding.ClosedEmbedding
import Langlands.GroupScheme.Reductive.DvrMatrixMonomorphismStatement

/-! # DVR matrix reduction using the proved PID embedding -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Raynaud affineness and the reductive matrix case suffice for the full DVR
case, using the proved linear embedding over DVRs. -/
def ReductiveDvrPidReductionStatement : Prop :=
  DvrGenericAffinenessStatement.{u} →
    ReductiveDvrMatrixMonomorphismStatement.{u} →
      ReductiveMonomorphismValuativeReduction.DvrCase.{u}

namespace DvrPidLinearEmbeddingReduction

/-- Embed the actual flat affine target over the DVR and cancel this closed
embedding after applying the supplied matrix case. -/
theorem flatAffineCase_of_matrixCase
    (matrix : ReductiveDvrMatrixMonomorphismStatement.{u}) :
    DvrAffineClosureReduction.FlatAffineCase.{u} := by
  intro R _ _ _ M G hM hflat ha hft _ f hf
  obtain ⟨N, ρ, hρ⟩ :=
    IntegralLinearEmbedding.exists_isClosedSubgroup_of_dvr R G hflat ha hft
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have hmono : Mono (ρ.restrict f).hom.hom.left := by
    change Mono (f.hom.hom.left ≫ ρ.hom.hom.left)
    infer_instance
  have hcomp : IsClosedImmersion (f.hom.hom.left ≫ ρ.hom.hom.left) :=
    matrix R M hM N (ρ.restrict f) hmono
  exact IsClosedImmersion.of_comp f.hom.hom.left ρ.hom.hom.left

/-- The full DVR reduction needs only Raynaud affineness and the matrix case
as geometric inputs. -/
theorem dvrCase_of_matrixCase
    (raynaud : DvrGenericAffinenessStatement.{u})
    (matrix : ReductiveDvrMatrixMonomorphismStatement.{u}) :
    ReductiveMonomorphismValuativeReduction.DvrCase.{u} :=
  DvrAffineClosureReduction.dvrCase_of_flatAffineCase raynaud
    (flatAffineCase_of_matrixCase matrix)

/-- The conditional PID-based reduction holds in every universe. -/
theorem reduction : ReductiveDvrPidReductionStatement.{u} :=
  dvrCase_of_matrixCase

end DvrPidLinearEmbeddingReduction
end Langlands.GroupScheme
