import Langlands.Representation.Classification.LeftCuspidalDerivative.Basic
import Langlands.Representation.Classification.LeftCuspidalDerivative.Product
import Langlands.Representation.Classification.LeftCuspidalDerivative.Pieces
import Langlands.Representation.Classification.LeftCuspidalDerivative.Segments
import Langlands.Representation.Classification.LeftCuspidalDerivative.Clause3
import Langlands.Representation.Classification.LeftCuspidalDerivative.Clause4

/-!
# The highest left cuspidal derivative lemma for `GL_n`: proof

Assembly of the five clauses of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`.
-/

noncomputable section

namespace Langlands.Classification.LeftCuspidalDerivative

universe uF uV

/-- **The highest left cuspidal derivative lemma for `GL_n`.** -/
theorem leftCuspidalDerivativeLemma : LeftCuspidalDerivativeLemma.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro d A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m Y Y' _ hY'Y hr
    exact leftReduced_of_isSubquotient F T A hY'Y hr
  · intro m₁ m₂ Y₁ Y₂ hY₁ hY₂ hr₁ hr₂
    exact leftReduced_binaryProduct F T binaryGeometricPieceConstituents.{uF, uV} A Y₁ Y₂ hY₁ hY₂
      hr₁ hr₂
  · intro K m π Y S hY hπ hS hr hYS hs
    exact comparison F T A K m π Y S hY hπ hS hr hYS hs
  · intro K m S π π' hS hr hπ hπ' hs hs'
    exact uniqueness F T A K m S π π' hS hr hπ hπ' hs hs'
  · intro κ hκ hA Δ π
    exact ⟨fun hπ hne => leftReduced_of_isSegmentHead F T A κ hκ hA Δ π hπ hne,
      fun hπ hne => leftReduced_of_isSegmentSocle F T A κ hκ hA Δ π hπ hne⟩

end Langlands.Classification.LeftCuspidalDerivative
