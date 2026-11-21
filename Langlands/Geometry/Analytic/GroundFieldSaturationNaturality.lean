import Langlands.Geometry.Analytic.GroundFieldSaturationComparison
import Langlands.Geometry.Analytic.GroundFieldExtensionReindexNaturality
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction

/-! # Naturality of the reverse saturation comparison -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, 0} K}

/-- Raise only the chart-index universe of a compatible strong map: the
generic reindexing along `Equiv.ulift` at both endpoints. -/
abbrev CompatibleStrongHom.liftOriginalIndices (f : CompatibleStrongHom A B) :
    CompatibleStrongHom A.saturationSource B.saturationSource :=
  f.reindex (Equiv.ulift : ULift.{v} A.atlas.Index ≃ A.atlas.Index)
    (Equiv.ulift : ULift.{v} B.atlas.Index ≃ B.atlas.Index)

/-- The Library's saturation extension of a compatible strong map, as a
compatible strong map between the literal saturated presentations. -/
def CompatibleStrongHom.saturatedCompatible (f : CompatibleStrongHom A B) :
    CompatibleStrongHom A.saturatedPresentation B.saturatedPresentation :=
  CompatibleStrongHom.ofSaturated f.saturationExtension A.atlas.saturatedAtlas_hasAllLocalDomains

/-- Lifting the original map agrees with mapping on the literal saturations,
via the reverse comparison, including the complete bounded pullbacks. -/
theorem saturatedToLiftedOriginal_natural (f : CompatibleStrongHom A B) :
    f.saturatedCompatible.comp B.saturatedToLiftedOriginal =
      A.saturatedToLiftedOriginal.comp f.liftOriginalIndices := by
  let FA := A.saturatedToLiftedOriginal
  let FB := B.saturatedToLiftedOriginal
  let F := f.saturatedCompatible
  let f' := f.liftOriginalIndices
  refine CompatibleStrongHom.ext ?_
  refine StrongHom.ext_of_saturated (f := (F.comp FB).toStrongHom)
    (g := (FA.comp f').toStrongHom) A.atlas.saturatedAtlas_hasAllLocalDomains rfl ?_
  intro S
  let i := (A.atlas.saturatedRepresentative S).index
  let I := A.atlas.originalSaturatedIndex i
  obtain ⟨j, hj⟩ := f.target_exists i
  let J := B.atlas.originalSaturatedIndex j
  have hFIJ := f.toStrongHom.saturationExtension_original_admissible i j hj
  have hS : range (A.saturatedPresentation.atlas.chart S) ⊆
      range (A.saturatedPresentation.atlas.chart I) := StrongHom.saturated_chart_subset_parent S
  have hFI : F.baseMap '' range (A.saturatedPresentation.atlas.chart I) ⊆
      range (B.saturatedPresentation.atlas.chart J) := hFIJ
  have hAi : FA.baseMap '' range (A.saturatedPresentation.atlas.chart I) ⊆
      range (A.saturationSource.atlas.chart (ULift.up i)) := A.saturatedToLiftedOriginal_admissible i
  have hBj : FB.baseMap '' range (B.saturatedPresentation.atlas.chart J) ⊆
      range (B.saturationSource.atlas.chart (ULift.up j)) := B.saturatedToLiftedOriginal_admissible j
  have hfi : f'.baseMap '' range (A.saturationSource.atlas.chart (ULift.up i)) ⊆
      range (B.saturationSource.atlas.chart (ULift.up j)) := hj
  have hI := F.toStrongHom.comp_admissible FB.toStrongHom I J (ULift.up j) hFI hBj
  have hI' := FA.toStrongHom.comp_admissible f'.toStrongHom I (ULift.up i) (ULift.up j) hAi hfi
  have hIS : (F.comp FB).baseMap '' range (A.saturatedPresentation.atlas.chart S) ⊆
      range (B.saturationSource.atlas.chart (ULift.up j)) := (image_mono hS).trans hI
  have hIS' : (FA.comp f').baseMap '' range (A.saturatedPresentation.atlas.chart S) ⊆
      range (B.saturationSource.atlas.chart (ULift.up j)) := (image_mono hS).trans hI'
  refine ⟨ULift.up j, hIS, ?_⟩
  have hleft := (F.comp FB).toStrongHom.restriction_comp_pullback S I (ULift.up j) hS hIS hI
  have hright := (FA.comp f').toStrongHom.restriction_comp_pullback S I (ULift.up j) hS hIS' hI'
  have hmain : (F.comp FB).pullback I (ULift.up j) hI =
      (FA.comp f').pullback I (ULift.up j) hI' := by
    rw [CompatibleStrongHom.comp_pullback F FB I J (ULift.up j) hFI hBj hI,
      CompatibleStrongHom.comp_pullback FA f' I (ULift.up i) (ULift.up j) hAi hfi hI']
    have hF := f.toStrongHom.saturationExtension_pullback_original f.coherent i j hj
    have hp₁ := BoundedAlgHom.comp_heq
      (A.atlas.saturatedAtlas_original_algebra i) (B.atlas.saturatedAtlas_original_algebra j) rfl
      hF (B.saturatedToLiftedOriginal_pullback_heq j)
    have hp₂ := BoundedAlgHom.comp_heq
      (A.atlas.saturatedAtlas_original_algebra i) rfl rfl
      (A.saturatedToLiftedOriginal_pullback_heq i) (heq_of_eq (rfl : f'.pullback (ULift.up i)
        (ULift.up j) hfi = f.pullback i j hj))
    have e₁ := hp₁.trans (heq_of_eq (BoundedAlgHom.comp_id (f.pullback i j hj)))
    have e₂ := hp₂.trans (heq_of_eq (BoundedAlgHom.id_comp (f.pullback i j hj)))
    exact eq_of_heq (e₁.trans e₂.symm)
  exact hleft.symm.trans ((congrArg (fun p =>
    (A.saturatedPresentation.atlas.restriction S I hS).comp p) hmain).trans hright)

namespace GroundFieldExtension

variable (L : Type*) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- Applying the actual scalar-extension functor retains the reverse
saturation naturality square. -/
theorem extendedSaturationComparison_natural (f : CompatibleStrongHom A B) :
    (compatibleMap K L f.saturatedCompatible).comp (extendedSaturationComparison B L) =
      (extendedSaturationComparison A L).comp (compatibleMap K L f.liftOriginalIndices) := by
  change (compatibleMap K L f.saturatedCompatible).comp
      (compatibleMap K L B.saturatedToLiftedOriginal) =
    (compatibleMap K L A.saturatedToLiftedOriginal).comp
      (compatibleMap K L f.liftOriginalIndices)
  rw [← compatibleMap_comp, ← compatibleMap_comp, saturatedToLiftedOriginal_natural]

end GroundFieldExtension
end Langlands.Analytic.AffinoidAtlasPresentation
