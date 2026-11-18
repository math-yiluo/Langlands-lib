import Langlands.GroupScheme.Reductive.AbsoluteFiniteCartanProof
import Langlands.LinearAlgebra.FiniteCartanClassification

/-! # Exact absolute Cartan classification of actual groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual absolute Cartan matrix of an absolutely almost-simple group
has an exact numbering by one of the nine finite irreducible families. -/
theorem absolutelyAlmostSimpleCartanClassification :
    AbsolutelyAlmostSimpleCartanClassificationStatement.{u} := by
  intro k _ G _ _ d hG
  classical
  let : Fintype d.Vertex := Fintype.ofFinite _
  let : DecidableEq d.Vertex := Classical.decEq _
  obtain ⟨hne, hfinite, hirr⟩ := absolutelyAlmostSimpleFiniteCartan k G d hG
  let := hne
  exact Langlands.LinearAlgebra.finiteCartanClassification
    d.Vertex (Matrix.of d.cartan) hfinite hirr

end Langlands.GroupScheme
