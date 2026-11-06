import Langlands.GroupScheme.Torus.NormCriterionCocycleTrivialization

/-! # Actual torus cocycle vanishing from the norm criterion -/

universe u

namespace Langlands.GroupScheme

/-- The unchanged finite-extension norm criterion trivializes every actual
scheme cocycle of every torus on every finite Galois field cover. -/
theorem dimensionLEOneTorusCocycleVanishing :
    DimensionLEOneTorusCocycleVanishingStatement.{u} := by
  intro K _ hK T hT L _ _ _ _ ξ
  exact hT.cocycle_isTrivial_of_dimensionLEOne K L T hK ξ

end Langlands.GroupScheme
