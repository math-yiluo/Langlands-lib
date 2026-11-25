/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing

/-!
# Restricting universal homeomorphisms to opens of the target

For a universal homeomorphism `f : X ⟶ Y` and an open `Y₀ ⊆ Y`, the restriction
`f ∣_ Y₀ : f ⁻¹ᵁ Y₀ ⟶ Y₀` is again a universal homeomorphism, and objects in the essential
image of base change along `f ∣_ Y₀` are in the essential image of base change along `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsUniversalHomeomorphism f] (Y₀ : Y.Opens)

/-- The restriction of a universal homeomorphism to an open of the target. -/
instance IsUniversalHomeomorphism.morphismRestrict : IsUniversalHomeomorphism (f ∣_ Y₀) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f Y₀).flip inferInstance

namespace Scheme.Hom

/-- Étale schemes over `f ⁻¹ᵁ Y₀`, viewed as étale schemes over `X`. -/
noncomputable abbrev etaleOfRestrict : (f ⁻¹ᵁ Y₀).toScheme.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (f ⁻¹ᵁ Y₀).ι)

/-- Étale schemes over `Y₀`, viewed as étale schemes over `Y`. -/
noncomputable abbrev etaleOfOpens : Y₀.toScheme.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale Y₀.ι)

/-- Base change along `f` of an étale `Y₀`-scheme is the base change along `f ∣_ Y₀`. -/
noncomputable def etaleObjEtaleOfOpensIso (V₀ : Y₀.toScheme.Etale) :
    f.Etale.obj ((etaleOfOpens Y₀).obj V₀) ≅
      (etaleOfRestrict f Y₀).obj ((f ∣_ Y₀).Etale.obj V₀) := by
  have H := (IsPullback.of_hasPullback V₀.hom (f ∣_ Y₀)).paste_vert
    (isPullback_morphismRestrict f Y₀)
  exact MorphismProperty.Over.isoMk H.isoPullback.symm H.isoPullback_inv_snd

omit [IsUniversalHomeomorphism f] in
/-- If `U₀` is in the essential image of base change along `f ∣_ Y₀`, then `U₀`, viewed as
an étale `X`-scheme, is in the essential image of base change along `f`. -/
lemma etale_essImage_etaleOfRestrict {U₀ : (f ⁻¹ᵁ Y₀).toScheme.Etale}
    (h : (f ∣_ Y₀).Etale.essImage U₀) : f.Etale.essImage ((etaleOfRestrict f Y₀).obj U₀) := by
  obtain ⟨V₀, ⟨e⟩⟩ := h
  exact ⟨(etaleOfOpens Y₀).obj V₀,
    ⟨etaleObjEtaleOfOpensIso f Y₀ V₀ ≪≫ (etaleOfRestrict f Y₀).mapIso e⟩⟩

/-- An étale `X`-scheme with empty underlying space is in the essential image of base change
along any morphism. -/
lemma etale_essImage_of_isEmpty {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Etale) [IsEmpty U.left] :
    f.Etale.essImage U := by
  have : IsEmpty (f.Etale.obj (Etale.mk (⊥ : Y.Opens).ι)).left := by
    constructor
    intro x
    exact (pullback.fst (⊥ : Y.Opens).ι f x).2
  exact ⟨Etale.mk (⊥ : Y.Opens).ι, ⟨MorphismProperty.Over.isoMk (asIso (isInitialOfIsEmpty.to _))
    (isInitialOfIsEmpty.hom_ext _ _)⟩⟩


end Scheme.Hom

end AlgebraicGeometry
