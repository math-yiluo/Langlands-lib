import Langlands.Representation.Plancherel.DynamicCommonLeviOrderedRadicals

open AlgebraicGeometry

namespace Langlands.Plancherel.DynamicCommonLeviComposition

universe u

/-- The ordered multiplication charts exist for every distance-additive triple
of dynamic radicals with a common Levi. -/
theorem distanceAdditiveRadicalFactorization :
    DistanceAdditiveRadicalFactorizationStatement.{u} := by
  intro F _ _ _ _ G _ _ hG ψ₀ ψ₁ ψ₂ h₁ h₂ hd
  let : Smooth G.X.hom := hG.smooth
  exact ⟨distanceAdditiveRadicalFactorizationData ψ₀ ψ₁ ψ₂ h₁ h₂ hd⟩

end Langlands.Plancherel.DynamicCommonLeviComposition
