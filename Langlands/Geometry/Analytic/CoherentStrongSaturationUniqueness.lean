import Langlands.Geometry.Analytic.CoherentStrongSaturationExtension
import Langlands.Geometry.Analytic.SaturatedStrongCategory

/-! # Uniqueness of the constructed whole-atlas extension -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- An extension has the same continuous map and recovers every supplied
original admissible bounded map. This is a property of the constructed output. -/
def IsSaturationExtension (f : StrongHom A B)
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) : Prop :=
  ∃ hb : F.baseMap = f.baseMap, ∀ (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
    HEq (F.pullback (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
      (by rw [hb]; exact f.saturationExtension_original_admissible i j h)) (f.pullback i j h)

/-- The actual construction meets the full original bounded recovery condition. -/
theorem saturationExtension_isSaturationExtension (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) : f.IsSaturationExtension (f.saturationExtension hf) :=
  ⟨rfl, f.saturationExtension_pullback_original hf⟩

/-- Every enlarged chart is contained in its representative's original parent. -/
theorem saturated_chart_subset_parent (S : A.atlas.localDomainFamily) :
    Set.range (A.atlas.saturatedChart S) ⊆ Set.range (A.atlas.saturatedChart
      (A.atlas.originalSaturatedIndex (A.atlas.saturatedRepresentative S).index)) := by
  rw [A.atlas.range_saturatedChart (A.atlas.originalSaturatedIndex
    (A.atlas.saturatedRepresentative S).index)]
  rintro _ ⟨x, rfl⟩
  exact ⟨(A.atlas.saturatedRepresentative S).domain.spectrumMap x, rfl⟩

/-- Naturality from an enlarged chart to its original parent and recovery
on original charts determine one enlarged pullback. Saturated-source
coherence then determines every other target pullback. -/
theorem saturationExtension_unique (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (hF : f.IsSaturationExtension F) : F = f.saturationExtension hf := by
  obtain ⟨hb, hp⟩ := hF
  let G := f.saturationExtension hf
  have hbG : F.baseMap = G.baseMap := hb
  refine ext_of_saturated A.atlas.saturatedAtlas_hasAllLocalDomains hbG ?_
  intro S
  let i := (A.atlas.saturatedRepresentative S).index
  obtain ⟨j, hj⟩ := f.target_exists i
  let I := A.atlas.originalSaturatedIndex i
  let J := B.atlas.originalSaturatedIndex j
  have hSI : Set.range (A.saturatedPresentation.atlas.chart S) ⊆
      Set.range (A.saturatedPresentation.atlas.chart I) := saturated_chart_subset_parent S
  have hIJ : F.baseMap '' Set.range (A.saturatedPresentation.atlas.chart I) ⊆
      Set.range (B.saturatedPresentation.atlas.chart J) := by
    rw [hb]
    exact f.saturationExtension_original_admissible i j hj
  have hSJ := (Set.image_mono hSI).trans hIJ
  have hIJG : G.baseMap '' Set.range (A.saturatedPresentation.atlas.chart I) ⊆
      Set.range (B.saturatedPresentation.atlas.chart J) := by rw [← hbG]; exact hIJ
  have hSJG : G.baseMap '' Set.range (A.saturatedPresentation.atlas.chart S) ⊆
      Set.range (B.saturatedPresentation.atlas.chart J) := by rw [← hbG]; exact hSJ
  have hpIJ : F.pullback I J hIJ = G.pullback I J hIJG :=
    eq_of_heq ((hp i j hj).trans (f.saturationExtension_pullback_original hf i j hj).symm)
  have hFp : (A.saturatedPresentation.atlas.restriction S I hSI).comp
      (F.pullback I J hIJ) = F.pullback S J hSJ := by
    simpa only [B.saturatedPresentation.atlas.restriction_id J Subset.rfl,
      BoundedAlgHom.comp_id] using
      F.restriction_comm S I J J hSI Subset.rfl hSJ hIJ
  have hGp : (A.saturatedPresentation.atlas.restriction S I hSI).comp
      (G.pullback I J hIJG) = G.pullback S J hSJG := by
    simpa only [B.saturatedPresentation.atlas.restriction_id J Subset.rfl,
      BoundedAlgHom.comp_id] using
      G.restriction_comm S I J J hSI Subset.rfl hSJG hIJG
  exact ⟨J, hSJ, hFp.symm.trans ((congrArg (fun q =>
    (A.saturatedPresentation.atlas.restriction S I hSI).comp q) hpIJ).trans hGp)⟩

/-- Actual existence and full algebraic uniqueness under the intrinsic law. -/
theorem existsUnique_saturationExtension (f : StrongHom A B) (hf : f.HasCoherentPullbacks) :
    ∃! F : StrongHom A.saturatedPresentation B.saturatedPresentation,
      f.IsSaturationExtension F :=
  ⟨f.saturationExtension hf, f.saturationExtension_isSaturationExtension hf,
    fun F hF => f.saturationExtension_unique hf F hF⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
