import Langlands.Representation.Classification.SupercuspidalEmbeddingTransport
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof

/-!
# Assembly of the supercuspidal embedding

Every irreducible smooth representation of a positive-rank general linear
group embeds into a normalized product of supercuspidal representations.
The field and supercuspidal-factor universes remain independent.
-/

noncomputable section

namespace Langlands

open PadicField.TopologicalData

universe uV uF

/-- Every irreducible smooth representation of `GL_n(F)`, for `n > 0`,
embeds into a product of supercuspidal representations. -/
theorem glSupercuspidalEmbedding :
    GLSupercuspidalEmbeddingStatement.{uV, uF} := by
  intro p hp F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ
  obtain ⟨_, B, σ, hσ, hcσ, j, hj⟩ :=
    CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T n π hπ
  obtain ⟨A, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviCuspidalFactorization.{uF, max uF uV, uV}
      p F T n hn B σ hσ hcσ
  exact T.exists_cuspidalSubrepresentation_of_levi_equiv B A σ.representation e π hπ j hj

end Langlands
