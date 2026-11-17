import Langlands.Geometry.Building.Kottwitz.TorusNaturalityStatement
import Langlands.Geometry.Building.Kottwitz.TorusNormNaturality
import Langlands.Geometry.Building.Kottwitz.TorusMapProof

/-! # Naturality of the actual torus Kottwitz homomorphisms -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- The norm characterization proves naturality for every actual morphism of tori. -/
theorem torusKottwitzNaturality : TorusKottwitzNaturalityStatement.{u} := by
  intro F _ _ _ _ k _ _ _ _ _ S T hS hT f x
  exact torusKottwitz_natural_of_existence F k hS hT f torusKottwitzExistence x

end Langlands.Geometry.Building.Kottwitz
