import Langlands.GroupScheme.Reductive.SteinbergCovariantReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SplitNecessity

/-! # Unconditional Steinberg tensor embeddings -/

universe u

namespace Langlands.GroupScheme

/-- Steinberg tensor embeddings, with all structural inputs discharged. -/
theorem steinbergTensorEmbedding : SteinbergTensorEmbeddingStatement.{u} :=
  steinbergTensorEmbedding_of_covariantExhaustion.{u}
    (steinbergCovariantExhaustion_of_bigCell.{u}
      (steinbergBigCell_of_rootAndCoroot.{u}
        rootDatumExistence.{u} splitSimplyConnectedCorootSpan.{u}))

end Langlands.GroupScheme
