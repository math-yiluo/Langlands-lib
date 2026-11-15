import Langlands.Geometry.Building.SpecialTorusIntegralModelStatement
import Langlands.Geometry.Building.SpecialTorusIntegralModelReduction
import Langlands.Geometry.Building.SpecialTorusBoundedModelProof

/-! # The integral model behind special tori (proof) -/

universe u

namespace Langlands.Geometry.Building

/-- **Kaletha–Prasad, Proposition 9.3.4 (building input).** For a connected reductive group
over a nonarchimedean local field and a maximal split torus `S`, there is a smooth affine
`𝒪[F]`-model with connected special fibre that contains a closed split `𝒪[F]`-torus with
generic fibre `S`, and whose base change to the maximal-unramified integers contains a closed
split torus whose generic fibre is a maximal `K`-split torus of `G_K`. -/
theorem specialTorusIntegralModel : SpecialTorusIntegralModelStatement.{u} :=
  specialTorusIntegralModelReductionStatement specialTorusBoundedModel

end Langlands.Geometry.Building
