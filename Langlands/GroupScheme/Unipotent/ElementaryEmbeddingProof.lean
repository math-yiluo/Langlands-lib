import Langlands.GroupScheme.Unipotent.ElementaryEmbeddingStatement
import Langlands.GroupScheme.Rational.SmoothCommutativePTorsionVectorEmbeddingProof
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.VectorGroupCoordinates

/-! # Smooth commutative groups of exponent `p` are elementary unipotent -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 14.49: a smooth commutative affine group killed by `p` over a field of
characteristic `p` has a closed embedding into a standard vector group. -/
theorem smoothExponentElementaryUnipotent : SmoothExponentElementaryUnipotentStatement.{u} := by
  intro k _ p _ _ G hSmooth hAffine hComm hExponent
  let commutativeG : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { toGrp := G, comm := hComm }
  obtain ⟨V, i, hi, n, hn⟩ := RelativeRoot.smoothCommutativePTorsionVectorEmbedding
    k p commutativeG hSmooth hAffine hExponent
  let e := hn.iso
  exact ⟨n, i ≫ e.hom, hi.comp_iso e⟩

end Langlands.GroupScheme
