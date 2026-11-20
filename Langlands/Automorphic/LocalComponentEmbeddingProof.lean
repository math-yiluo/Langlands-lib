import Langlands.Automorphic.LocalComponentEmbeddingReduction
import Langlands.Automorphic.LocalComponentExistenceProof

/-!
# Local components are the embedded irreducible representations

`LocalComponentEmbeddingStatement`, from the reduction
`localComponentEmbedding_of_localComponentExistence` and the proof
`localComponentExistence` of `LocalComponentExistenceStatement`.
-/

universe u uW

namespace Langlands

namespace Automorphic

/-- **Local components are the embedded irreducible representations** (Flath 1979, end of the
proof of Theorem 1, p.180), with no hypotheses. -/
theorem localComponentEmbedding : LocalComponentEmbeddingStatement.{u, uW} :=
  localComponentEmbedding_of_localComponentExistence localComponentExistence

end Automorphic

end Langlands
