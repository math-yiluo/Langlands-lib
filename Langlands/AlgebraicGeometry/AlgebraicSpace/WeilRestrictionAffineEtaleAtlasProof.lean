import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAtlasLocalRepresentation

/-! # Proof of the affine-atlas input for restriction of scalars of algebraic spaces -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Restriction along a finite projective algebra preserves the étale and surjective
properties of a finite-type affine scheme atlas of a quasi-separated algebraic space. -/
theorem weilRestrictionAffineEtaleAtlas : WeilRestrictionAffineEtaleAtlasStatement.{u} :=
  WeilRestrictionAtlas.weilRestrictionAffineEtaleAtlas_of_representationInput
    WeilRestrictionAtlas.representationInput

end Langlands.AlgebraicGeometry.AlgebraicSpace
