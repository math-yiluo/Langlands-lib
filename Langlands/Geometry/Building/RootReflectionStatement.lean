import Langlands.Geometry.Building.ParahoricBuildingAxioms

/-!
# The elements `m(u)` act on the apartment as affine reflections

KP Proposition 6.2.1 for the fixed apartment of building data: for every
relative root `a`, every `u ∈ U_a(F) ∖ {1}` and every opposite factor pair
`(u′, u″)` of `u`, the element `m(u) = u′ u u″` fixes the hyperplane
`H_u = {x | x_a(u) = 0}` pointwise. This is a Prop-valued target; it asserts
no existence of data.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Geometry.Building

/-- KP Proposition 6.2.1 on actual building data: for every nonarchimedean
local field `F` in universe `u`, every group scheme `G` over `F` with affine
structure morphism, and every `B : ValuationBuildingData G`, AS 1 holds with
the actual elements `m(u)`, that is `B.HasRootReflections`. No apartment
axiom beyond the data's valuation axioms is assumed. -/
def RootReflectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (B : ValuationBuildingData G),
    B.HasRootReflections

end Langlands.Geometry.Building
