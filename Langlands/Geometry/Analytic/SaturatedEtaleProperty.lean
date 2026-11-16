import Langlands.Geometry.Analytic.QuasiIsoTargetEtale

/-! # The étale property of actual saturated strong maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Test étaleness of a saturated strong map on its canonical actual
saturation extension, where full-recognition pieces are defined. -/
def strongEtale : MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K) :=
  fun A B f => StrongHom.IsEtaleAllPieces (A := A.presentation) (B := B.presentation)
    ((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f)

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- The canonical saturation extension of an actual strong quasi-isomorphism
is étale over all pieces. -/
theorem strongEtale_of_isQuasiIso (f : A ⟶ B) (hf : f.IsQuasiIso) : strongEtale f :=
  hf.saturationExtension_isEtaleAllPieces
    (f.hasCoherentPullbacks_of_saturated A.hasAllLocalDomains)

/-- Strong étaleness composes by functoriality of the actual saturation
extension and composition of all-piece étaleness. -/
theorem strongEtale_comp {f : A ⟶ B} {g : B ⟶ C}
    (hf : strongEtale f) (hg : strongEtale g) : strongEtale (f ≫ g) := by
  unfold strongEtale at hf hg ⊢
  rw [Functor.map_comp]
  exact hf.comp hg

instance : (strongEtale (K := K) :
    MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).IsMultiplicative where
  id_mem A := strongEtale_of_isQuasiIso (𝟙 A)
    (AffinoidAtlasPresentation.StrongHom.isQuasiIso_id A.presentation)
  comp_mem _ _ hf hg := strongEtale_comp hf hg

/-- Source denominators preserve and reflect the canonical strong étale property. -/
theorem strongEtale_precomp_quasiIso_iff {f : A ⟶ B} {g : B ⟶ C}
    (hf : f.IsQuasiIso) : strongEtale (f ≫ g) ↔ strongEtale g := by
  unfold strongEtale
  rw [Functor.map_comp]
  exact StrongHom.isEtaleAllPieces_precomp_quasiIso_iff
    (hf.saturationExtension (f.hasCoherentPullbacks_of_saturated A.hasAllLocalDomains))

/-- Target denominators preserve and reflect the canonical strong étale property. -/
theorem strongEtale_postcomp_quasiIso_iff {f : A ⟶ B} {g : B ⟶ C}
    (hg : g.IsQuasiIso) : strongEtale (f ≫ g) ↔ strongEtale f := by
  unfold strongEtale
  rw [Functor.map_comp]
  exact StrongHom.isEtaleAllPieces_postcomp_quasiIso_iff
    (hg.saturationExtension (g.hasCoherentPullbacks_of_saturated B.hasAllLocalDomains))

end Langlands.Analytic.SaturatedAtlasPresentation
