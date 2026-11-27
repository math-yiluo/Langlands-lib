import Langlands.GroupScheme.Reductive.MonomorphismDvrReduction
import Langlands.GroupScheme.Reductive.DvrPidLinearEmbeddingReduction
import Langlands.GroupScheme.Reductive.DvrGenericClosureIsomorphism
import Langlands.GroupScheme.DvrGenericAffinenessProof

/-! # Proof: monomorphisms out of reductive group schemes are closed immersions

The arbitrary-base reduction `ReductiveMonomorphismDvrReduction.generalCase_of_dvrCase`
applied to the case of a discrete valuation ring, which
`DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase` derives from Raynaud's affineness
criterion `dvrGenericAffineness` and the matrix case `ReductiveGenericClosure.dvrMatrixCase`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Monomorphisms out of reductive group schemes are closed immersions** (Conrad,
*Reductive group schemes* (2014), Theorem 5.3.5, first sentence), in every universe: for a
reductive group `G` over an arbitrary scheme `S` and a separated `S`-group `G'` of finite
presentation, every homomorphism `G ⟶ G'` whose underlying morphism of schemes is a
monomorphism is a closed immersion. -/
theorem reductiveMonomorphismClosedImmersion :
    ReductiveMonomorphismClosedImmersionStatement.{u} :=
  ReductiveMonomorphismDvrReduction.generalCase_of_dvrCase
    (DvrPidLinearEmbeddingReduction.dvrCase_of_matrixCase
      dvrGenericAffineness ReductiveGenericClosure.dvrMatrixCase)

end Langlands.GroupScheme
