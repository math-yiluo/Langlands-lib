import Langlands.GroupScheme.DvrGenericAffinenessStatement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The smooth case of Raynaud's DVR affineness criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth separated finite-type group scheme over a DVR with affine actual
generic fibre is affine. -/
def SmoothDvrGenericAffinenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Smooth G.X.hom → QuasiCompact G.X.hom → IsSeparated G.X.hom →
    IsAffineHom
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj G).X.hom →
    IsAffineHom G.X.hom

end Langlands.GroupScheme
