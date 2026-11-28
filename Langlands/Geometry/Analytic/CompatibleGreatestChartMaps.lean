import Langlands.Geometry.Analytic.LocalizedSaturationEquivalence
import Langlands.Geometry.Analytic.TopChartSpectralTests

/-! # Compatible localized maps into a greatest chart -/

noncomputable section

universe u v

namespace Langlands.Analytic.CompatibleAtlasPresentation

open CategoryTheory Set
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : CompatibleAtlasPresentation.{u, v, v} K}

private theorem saturated_greatest
    (j : B.presentation.atlas.Index)
    (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j))
    (s : (saturationFunctor.obj B).presentation.atlas.Index) :
    range ((saturationFunctor.obj B).presentation.atlas.chart s) ⊆
      range ((saturationFunctor.obj B).presentation.atlas.chart
        (B.presentation.atlas.originalSaturatedIndex j)) := by
  change range (B.presentation.atlas.saturatedChart s) ⊆
    range (B.presentation.atlas.saturatedChart (B.presentation.atlas.originalSaturatedIndex j))
  rw [B.presentation.atlas.range_saturatedChart (B.presentation.atlas.originalSaturatedIndex j)]
  intro x _
  obtain ⟨k, hk⟩ := B.presentation.atlas.exists_mem_range_chart x
  exact hj k hk

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
/-- A localized map into a presentation with a greatest chart has a unique
compatible strong representative on the original source. -/
def localizedGreatestChartHomEquiv
    (j : B.presentation.atlas.Index)
    (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j)) :
    (A ⟶ B) ≃ (localizationFunctor.obj A ⟶ localizationFunctor.obj B) := by
  let L : LocalizedCategory.{u, v, v} (K := K) ⥤
      SaturatedAtlasPresentation.LocalizedCategory.{u, v, v} (K := K) :=
    localizedSaturationFunctor
  let e₁ : (A ⟶ B) ≃ (saturationFunctor.obj A ⟶ saturationFunctor.obj B) :=
    AffinoidAtlasPresentation.CompatibleStrongHom.saturationExtensionEquiv
      (A := A.presentation) (B := B.presentation)
  let e₂ := SaturatedAtlasPresentation.localizedTopTargetHomEquiv
    (A := saturationFunctor.obj A) (B := saturationFunctor.obj B)
    (B.presentation.atlas.originalSaturatedIndex j) (saturated_greatest (B := B) j hj)
  let e₃ := (Functor.FullyFaithful.ofFullyFaithful L).homEquiv
    (X := localizationFunctor.obj A) (Y := localizationFunctor.obj B)
  exact e₁.trans (e₂.trans e₃.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
@[simp]
theorem localizedGreatestChartHomEquiv_apply
    (j : B.presentation.atlas.Index)
    (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j))
    (f : A ⟶ B) :
    localizedGreatestChartHomEquiv (A := A) (B := B) j hj f = localizationFunctor.map f := by
  let L : LocalizedCategory.{u, v, v} (K := K) ⥤
      SaturatedAtlasPresentation.LocalizedCategory.{u, v, v} (K := K) :=
    localizedSaturationFunctor
  let e := (Functor.FullyFaithful.ofFullyFaithful L).homEquiv
    (X := localizationFunctor.obj A) (Y := localizationFunctor.obj B)
  apply e.injective
  change e (e.symm _) = localizedSaturationFunctor.map (localizationFunctor.map f)
  rw [Equiv.apply_symm_apply, SaturatedAtlasPresentation.localizedTopTargetHomEquiv_apply,
    localizedSaturationFunctor_map]
  rfl

/-- The bounded pullback from a greatest target chart to an original source chart. -/
def greatestChartPullback (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j))
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B) :
    BoundedAlgHom K (B.presentation.atlas.algebra j) (A.presentation.atlas.algebra i) :=
  ((localizedGreatestChartHomEquiv (A := A) (B := B) j hj).symm f).toStrongHom.pullbackAtTop j hj i

@[simp]
theorem greatestChartPullback_map (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (hj : ∀ k, range (B.presentation.atlas.chart k) ⊆ range (B.presentation.atlas.chart j))
    (f : A ⟶ B) :
    greatestChartPullback i j hj (localizationFunctor.map f) =
      f.toStrongHom.pullbackAtTop j hj i := by
  apply congrArg (fun g : A ⟶ B => g.toStrongHom.pullbackAtTop j hj i)
  rw [← localizedGreatestChartHomEquiv_apply j hj f, Equiv.symm_apply_apply]

@[simp]
theorem greatestChartPullback_id (i : A.presentation.atlas.Index)
    (hi : ∀ k, range (A.presentation.atlas.chart k) ⊆ range (A.presentation.atlas.chart i)) :
    greatestChartPullback i i hi (𝟙 (localizationFunctor.obj A)) =
      BoundedAlgHom.id K (A.presentation.atlas.algebra i) := by
  rw [← localizationFunctor.map_id A, greatestChartPullback_map]
  exact A.presentation.atlas.restriction_id i (subset_rfl)

theorem greatestChartPullback_comp
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index) (k : C.presentation.atlas.Index)
    (hj : ∀ l, range (B.presentation.atlas.chart l) ⊆ range (B.presentation.atlas.chart j))
    (hk : ∀ l, range (C.presentation.atlas.chart l) ⊆ range (C.presentation.atlas.chart k))
    (f : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (g : localizationFunctor.obj B ⟶ localizationFunctor.obj C) :
    greatestChartPullback i k hk (f ≫ g) =
      (greatestChartPullback i j hj f).comp (greatestChartPullback j k hk g) := by
  let a := (localizedGreatestChartHomEquiv (A := A) (B := B) j hj).symm f
  let b := (localizedGreatestChartHomEquiv (A := B) (B := C) k hk).symm g
  have ha : localizationFunctor.map a = f := by
    rw [← localizedGreatestChartHomEquiv_apply j hj a]
    exact Equiv.apply_symm_apply _ _
  have hb : localizationFunctor.map b = g := by
    rw [← localizedGreatestChartHomEquiv_apply k hk b]
    exact Equiv.apply_symm_apply _ _
  rw [← ha, ← hb, ← localizationFunctor.map_comp, greatestChartPullback_map,
    greatestChartPullback_map, greatestChartPullback_map]
  exact a.comp_pullback b i j k (a.toStrongHom.image_chart_top j hj i)
    (b.toStrongHom.image_chart_top k hk j) ((a ≫ b).toStrongHom.image_chart_top k hk i)

end Langlands.Analytic.CompatibleAtlasPresentation
