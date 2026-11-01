import Langlands.AlgebraicGeometry.Picard.AffineOpenImmersionLineBundleExtensionStatement
import Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleIdealEmbeddingStatement
import Langlands.AlgebraicGeometry.Picard.OpenImmersionInvertibleIdealExtensionStatement

/-! # Assembling affine extension from two invertible-ideal inputs -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

/-- The two invertible-ideal inputs imply the affine-target extension statement. -/
def affineOpenImmersionLineBundleExtension_of_ideals
    (hEmbedding : QuasiAffineLineBundleIdealEmbeddingStatement.{u})
    (hExtension : OpenImmersionInvertibleIdealExtensionStatement.{u}) :
    AffineOpenImmersionLineBundleExtensionStatement.{u} := by
  intro X hX hAffine Y j hOpen hFactor D
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isOpenImmersion j
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : NoetherianSpace X := noetherianSpace_of_isAffine
  have : NoetherianSpace Y := j.isOpenEmbedding.isInducing.noetherianSpace
  have : Scheme.IsQuasiAffine Y := Scheme.IsQuasiAffine.of_isImmersion j
  obtain ⟨s, hs⟩ := hEmbedding Y D
  have : Mono s := hs
  obtain ⟨E, t, ht, e, he⟩ := hExtension X Y j hFactor D s
  exact ⟨E, ⟨e⟩⟩

end Langlands.AlgebraicGeometry.Picard
