import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionDiagonalProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionAffineEtaleAtlasProof

/-! # Weil restriction of algebraic spaces along finite locally free maps -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Lemma 5.10: finite locally free restriction of scalars preserves
quasi-separated algebraic spaces of finite type, with separatedness and finite
presentation when present. -/
theorem spaceWeilRestriction : SpaceWeilRestrictionStatement.{u} :=
  spaceWeilRestriction_of_geometricInputs
    weilRestrictionDiagonal_proof weilRestrictionAffineEtaleAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
