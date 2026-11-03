import Langlands.GroupScheme.Rational.StandardLeviPointComparison
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Proof of the canonical versus inherited standard-Levi point topology

Postcomposition with the closed immersion `j` is an embedding of identity-test
points. Its composite with the inclusion of `standardLeviPoints` is that
postcomposition, so the bijective point equivalence is a homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

/-- The explicit rational-point equivalence of every closed represented standard
Levi is a homeomorphism from the canonical topology to the inherited topology. -/
theorem standardLeviPointTopologyComparisonStatement_proof :
    StandardLeviPointTopologyComparisonStatement.{u} := by
  intro F _ _ G hG T i _hi ν _hν J _hJ M hM j hc hj
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffineHom M.X.hom := hM.isAffineHom
  have : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have : IsClosedImmersion j.hom.hom.left := hc
  let : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (standardLeviPoints i ν J) := standardLeviPointTopology i ν J
  change IsHomeomorph (standardLeviRationalPointsEquiv i ν J j hj)
  have hval : IsInducing (fun x : standardLeviPoints i ν J => (x : rationalPoints G)) :=
    ⟨rfl⟩
  have hcomp : IsInducing ((fun x : standardLeviPoints i ν J => (x : rationalPoints G)) ∘
      standardLeviRationalPointsEquiv i ν J j hj) :=
    (isEmbedding_rationalPointMap F j.hom.hom).isInducing
  refine isHomeomorph_iff_isEmbedding_surjective.mpr ⟨⟨hval.of_comp_iff.mp hcomp, ?_⟩, ?_⟩
  · exact (standardLeviRationalPointsEquiv i ν J j hj).injective
  · exact (standardLeviRationalPointsEquiv i ν J j hj).surjective

end Langlands.GroupScheme
