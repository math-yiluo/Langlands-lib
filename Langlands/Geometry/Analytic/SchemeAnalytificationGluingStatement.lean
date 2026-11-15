import Langlands.Geometry.Analytic.SchemeAnalytificationSpace
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Statement: the glued analytification space of a scheme is an open gluing -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology

/-- Statement (Berkovich 1990, proof of Theorem 3.4.1, steps (2)–(3), and Theorem
3.4.8(i), for the Library's polynomial-locus model): for a complete nonarchimedean
nontrivially normed field `K` and a scheme `X` locally of finite type over `K`,
(1) the maps of affine analytifications induced by inclusions of affine opens are
open embeddings; (2) every canonical map from the analytification of an affine open
into the glued space is an open embedding; (3) the images of two affine opens meet
exactly in the union of the images of the affine opens contained in both; (4) when
`X` is affine, the canonical map from the analytification of `⊤` is a homeomorphism;
(5) `X` is separated over `K` if and only if the glued space is Hausdorff. -/
def SchemeAnalytificationGluingStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f],
    (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U), IsOpenEmbedding (localMap K f h)) ∧
    (∀ U : X.affineOpens, IsOpenEmbedding (ι K f U)) ∧
    (∀ U V : X.affineOpens, Set.range (ι K f U) ∩ Set.range (ι K f V) =
      ⋃ (W : X.affineOpens) (_ : (W : X.Opens) ≤ (U : X.Opens) ⊓ V), Set.range (ι K f W)) ∧
    (∀ [IsAffine X], IsHomeomorph (ι K f ⟨⊤, isAffineOpen_top X⟩)) ∧
    (IsSeparated f ↔ T2Space (Space K f))

end Langlands.Analytic.SchemeAnalytification
