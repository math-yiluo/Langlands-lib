import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.SpecialTorusExistenceFromModel
import Langlands.Geometry.Building.SpecialTorusIntegralModelProof

/-! # Existence of special tori (KP Proposition 9.3.4, proof) -/

universe u

namespace Langlands.Geometry.Building

/-- **Kaletha–Prasad, Proposition 9.3.4.** Every maximal split torus `S` of a connected
reductive group `G` over a nonarchimedean local field `F` lies in a closed commutative subgroup
`T` of `G` whose base change to the maximal unramified extension `K` is a maximal `K`-split
torus of `G_K`. -/
theorem specialTorusExistence : SpecialTorusExistenceStatement.{u} :=
  specialTorusExistence_of_integralModel specialTorusIntegralModel

end Langlands.Geometry.Building
