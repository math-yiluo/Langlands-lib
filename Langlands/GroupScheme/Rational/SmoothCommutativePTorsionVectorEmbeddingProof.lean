import Langlands.GroupScheme.Rational.CommutativePTorsionEmbeddingStatement
import Langlands.GroupScheme.Rational.SmoothPTorsionPrimitiveGenerators
import Langlands.GroupScheme.Rational.PrimitiveVectorEmbedding

/-! # Arbitrary-field vector embeddings of smooth commutative p-torsion groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- A smooth commutative affine group killed by `p` embeds as a closed subgroup
of a finite-dimensional vector group over the original field. -/
theorem smoothCommutativePTorsionVectorEmbedding :
    SmoothCommutativePTorsionVectorEmbeddingStatement.{u} := by
  intro k _ p _ _ G hSmooth hAff hG
  have := hSmooth
  have := hAff
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  have : Algebra.FiniteType k A := AffineCoordinates.algebraFiniteType G.toGrp
  obtain ⟨n, j, hj⟩ :=
    HopfPrimitive.exists_closed_vectorEmbedding_of_primitive_generation A
      (AffineCoordinates.adjoin_primitive_eq_top_of_smooth_uniformExponent G.toGrp p hG)
  let e := AffineCoordinates.hopfSpecIso G.toGrp
  refine ⟨VectorGroup.groupScheme (CommRingCat.of k) n, e.inv ≫ j, ?_, n, ?_⟩
  · have : IsClosedImmersion j.hom.hom.left := hj
    have : IsIso e.inv.hom.hom.left :=
      (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map e.inv))
    change IsClosedImmersion (e.inv.hom.hom.left ≫ j.hom.hom.left)
    infer_instance
  · exact ⟨VectorGroup.coordinates (CommRingCat.of k) n,
      VectorGroup.isNaturalVectorCoordinates⟩

end Langlands.GroupScheme.RelativeRoot
