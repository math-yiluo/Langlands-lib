import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealSections
import Langlands.AlgebraicGeometry.Picard.OpenImmersionIdealLocalFreeness
import Langlands.AlgebraicGeometry.Picard.OpenImmersionInvertibleIdealExtensionStatement

/-! # Extension of an invertible ideal with factorial complementary stalks -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual inverse-image ideal closure is invertible under complementary factoriality. -/
theorem openImmersionInvertibleIdealExtension :
    OpenImmersionInvertibleIdealExtensionStatement.{u} := by
  intro X _ Y j _ hUFD D s hs
  let E : LineBundle X := ⟨OpenImmersionIdeal.closure j s,
    OpenImmersionIdeal.isLocallyFreeRankOne_of_range_iff j hUFD D s
      (OpenImmersionIdeal.closure j s) (OpenImmersionIdeal.inclusion j s)
      (OpenImmersionIdeal.inclusion_range_iff j s)⟩
  refine ⟨E, OpenImmersionIdeal.inclusion j s, inferInstance,
    OpenImmersionIdeal.restrictionIso j s, ?_⟩
  exact OpenImmersionIdeal.restrictionIso_hom_inclusion j s

end Langlands.AlgebraicGeometry.Picard
