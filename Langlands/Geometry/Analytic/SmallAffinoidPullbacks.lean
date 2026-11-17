import Langlands.Geometry.Analytic.AffineTopChartPullbacks
import Langlands.Geometry.Analytic.SmallAffinoidPointwiseSquare
import Langlands.Geometry.Analytic.CompatibleStrongOriginalRestriction
import Langlands.Geometry.Analytic.LocalizedPullbackDescent

/-! # Full categorical pullbacks of small actual affinoid spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory CategoryTheory.Limits Set PresentedAffinoidAlgebra
open AffinoidAtlasPresentation SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The original whole spectrum is a chart in its actual saturation. -/
def topIndex (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.Index :=
  (presentation R).atlas.originalSaturatedIndex PUnit.unit

/-- The retained whole-spectrum chart still covers the entire ambient space. -/
theorem range_topIndex (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    Set.range ((saturated R).presentation.atlas.chart (topIndex R)) = Set.univ := by
  change Set.range ((presentation R).atlas.saturatedAtlas.chart
    ((presentation R).atlas.originalSaturatedIndex PUnit.unit)) = Set.univ
  exact ((presentation R).atlas.saturatedAtlas_original_range PUnit.unit).trans
    (spectrumHomeomorph R).surjective.range_eq

/-- Every saturated local domain lies in the original whole-spectrum chart. -/
theorem top_contains (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)]
    (i : (saturated R).presentation.atlas.Index) :
    Set.range ((saturated R).presentation.atlas.chart i) ⊆
      Set.range ((saturated R).presentation.atlas.chart (topIndex R)) := by
  rw [range_topIndex]
  exact Set.subset_univ _

/-- The original greatest chart retains the original presented algebra. -/
theorem top_algebra (R : PresentedAffinoidAlgebra K) [Small.{v} (BanachSpectrum R)] :
    (saturated R).presentation.atlas.algebra (topIndex R) = R :=
  (presentation R).atlas.saturatedAtlas_original_algebra PUnit.unit

/-- Saturation retains the complete original bounded map at the two top charts. -/
theorem map_pullbackAtTop_heq {R S : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum R)] [Small.{v} (BanachSpectrum S)]
    (f : BoundedAlgHom K R S) :
    HEq ((map f).pullbackAtTop (topIndex R) (top_contains R) (topIndex S)) f := by
  have h := (strongMap f).image_chart_top PUnit.unit
    (fun j => by cases j; exact Subset.rfl) PUnit.unit
  exact (strongMap f).saturationExtension_pullback_original
    (strongMap_coherent f) PUnit.unit PUnit.unit h

private theorem existsUnique_lift_transport
    {A B C P' B' C' A' : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
    (hP : P' = AffinoidPushout.algebra f g) (hB : B' = B) (hC : C' = C) (hA : A' = A)
    (p : BoundedAlgHom K B' P') (q : BoundedAlgHom K C' P')
    (f' : BoundedAlgHom K A' B') (g' : BoundedAlgHom K A' C')
    (hp : HEq p (AffinoidPushout.leftMap f g))
    (hq : HEq q (AffinoidPushout.rightMap f g)) (hf : HEq f' f) (hg : HEq g' g) :
    ∀ (E : PresentedAffinoidAlgebra K)
      (α : BoundedAlgHom K B' E) (β : BoundedAlgHom K C' E),
      α.comp f' = β.comp g' →
        ∃! ℓ : BoundedAlgHom K P' E, ℓ.comp p = α ∧ ℓ.comp q = β := by
  cases hP
  cases hB
  cases hC
  cases hA
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq hf
  cases eq_of_heq hg
  intro E α β hcompat
  exact AffinoidPushout.existsUnique_lift f g E α β hcompat

section Pushout

variable {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
  [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
  [Small.{v} (BanachSpectrum C)]

/-- The actual bounded pushout supplies universality at the retained greatest
charts, with all original bounded maps retained under saturation. -/
theorem pushout_topChartPushout
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    TopChartPushout (pushoutFst f g) (pushoutSnd f g) (map f) (map g)
      (topIndex (AffinoidPushout.algebra f g)) (topIndex B) (topIndex C) (topIndex A)
      (top_contains B) (top_contains C) (top_contains A) := by
  exact existsUnique_lift_transport f g
    (top_algebra (AffinoidPushout.algebra f g)) (top_algebra B)
    (top_algebra C) (top_algebra A) _ _ _ _
    (map_pullbackAtTop_heq (AffinoidPushout.leftMap f g))
    (map_pullbackAtTop_heq (AffinoidPushout.rightMap f g))
    (map_pullbackAtTop_heq f) (map_pullbackAtTop_heq g)

/-- The concrete small affinoid square is a pullback on complete strong
morphisms from every saturated test presentation. -/
theorem pushout_isPullback
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    IsPullback (pushoutFst f g) (pushoutSnd f g) (map f) (map g) :=
  (pushout_topChartPushout f g).isPullback
    (top_contains (AffinoidPushout.algebra f g)) (pushout_condition f g)

/-- The strict strong universal property supplies refined strong universality
using the identity source refinement. -/
theorem pushout_isRefinedStrongPullback
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    IsRefinedStrongPullback (pushoutFst f g) (pushoutSnd f g) (map f) (map g) := by
  let h := pushout_topChartPushout f g
  let hP := top_contains (AffinoidPushout.algebra f g)
  refine ⟨pushout_condition f g, ?_, ?_⟩
  · intro T a b hab
    obtain ⟨l, hl, _⟩ := h.existsUnique_lift hP a b hab
    refine ⟨T, 𝟙 T, AffinoidAtlasPresentation.StrongHom.isQuasiIso_id T.presentation,
      l, ?_, ?_⟩
    · simpa only [Category.id_comp] using hl.1
    · simpa only [Category.id_comp] using hl.2
  · intro T a b hp hq
    exact h.hom_ext hP (pushout_condition f g) a b hp hq

/-- The same small affinoid square is an actual pullback against arbitrary
localized test morphisms, including fractions. -/
theorem pushout_localized_isPullback
    [Small.{v} (BanachSpectrum (AffinoidPushout.algebra f g))] :
    IsPullback (localizationFunctor.map (pushoutFst f g))
      (localizationFunctor.map (pushoutSnd f g))
      (localizationFunctor.map (map f)) (localizationFunctor.map (map g)) :=
  (pushout_isRefinedStrongPullback f g).isPullback

/-- Finite Banach base change gives the small actual affinoid pullback with
its complete strong universal property. No etaleness is asserted. -/
theorem exists_finite_isPullback
    (h : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach) :
    ∃ (P : SaturatedAtlasPresentation.{u, v, v} K)
      (p : P ⟶ saturated B) (q : P ⟶ saturated C),
      IsPullback p q (map f) (map g) ∧
        IsRefinedStrongPullback p q (map f) (map g) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g h hf
  exact ⟨pushout f g, pushoutFst f g, pushoutSnd f g,
    pushout_isPullback f g, pushout_isRefinedStrongPullback f g⟩

/-- The finite Banach hypothesis also supplies a pullback in the actual
localized category, with its object in the same independent space universe. -/
theorem exists_finite_localized_isPullback
    (h : AffinoidPushout.FiniteBanachPushoutStatement K) (hf : f.IsFiniteBanach) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K))
      (p : P ⟶ localizationFunctor.obj (saturated B))
      (q : P ⟶ localizationFunctor.obj (saturated C)),
      IsPullback p q (localizationFunctor.map (map f))
        (localizationFunctor.map (map g)) := by
  let := AffinoidPushout.small_spectrum_of_finiteBanachPushout f g h hf
  exact ⟨localizationFunctor.obj (pushout f g),
    localizationFunctor.map (pushoutFst f g),
    localizationFunctor.map (pushoutSnd f g), pushout_localized_isPullback f g⟩

end Pushout

end Langlands.Analytic.SmallAffinoidSpectrum
