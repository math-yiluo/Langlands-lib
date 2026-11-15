import Langlands.GroupScheme.ZExtensionMorphismDominationProof

/-! # Common domination of two actual z-extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The identity-map specialization of morphism-compatible domination. -/
theorem zExtensionCommonDomination : ZExtensionCommonDominationStatement.{u} := by
  intro k _ G hG z t
  obtain ⟨w, r, s, hr, hs⟩ :=
    zExtensionMorphismDomination k G G hG hG z t (𝟙 G)
  exact ⟨w, r, s, hr, by simpa only [Category.comp_id] using hs⟩

end Langlands.GroupScheme
