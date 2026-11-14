import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalEmbeddingTransport
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalEmbeddingProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalEmbeddingProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ
open Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uV uF

/-- Every irreducible smooth representation of `GL_n(F)`, for `n > 0`,
embeds into a product of supercuspidal representations. -/
theorem glSupercuspidalEmbedding :
    GLSupercuspidalEmbeddingStatement.{uV, uF} := by
  intro F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ
  obtain ⟨_, B, σ, hσ, hcσ, j, hj⟩ :=
    CuspidalSupport.cuspidalEmbedding.{uF, max uF uV} F T n π hπ
  obtain ⟨A, ⟨e⟩⟩ :=
    CuspidalSupport.padicLeviCuspidalFactorization.{uF, max uF uV, uV}
      F T n hn B σ hσ hcσ
  exact T.exists_cuspidalSubrepresentation_of_levi_equiv B A σ.representation e π hπ j hj

end Langlands.AllFieldBZ
