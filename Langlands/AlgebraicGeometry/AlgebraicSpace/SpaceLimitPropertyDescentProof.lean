import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitProperDescentOfSchemeCovers
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCoverProof

/-! # Descent of eight properties of algebraic-space morphisms along limits -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's eight published property-descent clauses for finitely presented algebraic spaces. -/
theorem spaceLimitPropertyDescent : SpaceLimitPropertyDescentStatement.{u} :=
  spaceLimitPropertyDescent_of_foundations representedAtlasEffectivity properSchemeCover

end Langlands.AlgebraicGeometry.AlgebraicSpace
