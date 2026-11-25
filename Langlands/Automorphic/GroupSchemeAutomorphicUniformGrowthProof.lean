import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof
import Langlands.Automorphic.GroupSchemeAdaptedCasimirProof

/-!
# Every actual adelic automorphic form has uniformly moderate growth

A proof of `Langlands.Automorphic.GroupSchemeFunctions.AdelicAutomorphicUniformGrowthStatement`:
the Library's reduction `adelicAutomorphicUniformGrowthReduction` applied to the interior
estimate for elliptic left-invariant word operators on Lie groups
(`Langlands.Geometry.Manifold.lieGroupEllipticInteriorEstimate`, at universes `u, u`) and to the
adapted Casimir element on the infinite adelic points (`adelicAdaptedCasimir`). See the paired
Markdown.
-/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- **Mœglin–Waldspurger 1995, I.2.17, case `P = G`.** For a connected reductive group `G` over a
number field, a maximal compact subgroup `Kinf` of the infinite adelic points and a closed
matrix representation `rho` with `0 < N`, every actual adelic automorphic form (`Kinf`-finite,
centre-finite, of moderate growth) has uniformly moderate growth: one real exponent bounds every
derivative by an element of the actual enveloping algebra. -/
theorem adelicAutomorphicUniformGrowth : AdelicAutomorphicUniformGrowthStatement.{u} :=
  adelicAutomorphicUniformGrowthReduction.{u}
    Langlands.Geometry.Manifold.lieGroupEllipticInteriorEstimate.{u, u} adelicAdaptedCasimir.{u}

end Langlands.Automorphic.GroupSchemeFunctions
