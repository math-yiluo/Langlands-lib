import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.Derived.CommutatorEnvelope
import Langlands.GroupScheme.ImageGenerationReducedStatement
import Langlands.AlgebraicGeometry.SmoothGeometricallyReducedProof

/-! # Reduction of derived-subgroup smoothness to reduced-source generation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option linter.defProp false in
set_option backward.isDefEq.respectTransparency.types false in
/-- General smooth generation from a geometrically reduced affine source implies
the exact derived-subgroup smoothness target. -/
def derivedSubgroupSmoothness_of_reducedImageGeneration
    (hGeneration : GeometricallyReducedAffineImageGenerationStatement.{u}) :
    DerivedSubgroupSmoothnessStatement.{u} := by
  intro k _ G _ _ D d hd hG
  let : Smooth G.X.hom := hG
  let V := G.X ⊗ G.X
  have hVAff : IsAffineHom V.hom := by
    change IsAffineHom (pullback.fst G.X.hom G.X.hom ≫ G.X.hom)
    let : IsAffineHom (pullback.fst G.X.hom G.X.hom) :=
      MorphismProperty.pullback_fst _ _ inferInstance
    infer_instance
  have hVSm : Smooth V.hom := by
    change Smooth (pullback.fst G.X.hom G.X.hom ≫ G.X.hom)
    infer_instance
  let : Smooth V.hom := hVSm
  have hVRed : GeometricallyReduced V.hom :=
    Langlands.AlgebraicGeometry.smoothGeometricallyReduced _ _ _ hVSm
  obtain ⟨E, hE⟩ := hGeneration k G V hVAff inferInstance hVRed
    (commutatorMap (𝟙 G) (𝟙 G))
  exact hd.smooth_of_generatedImage E hE

end Langlands.GroupScheme
