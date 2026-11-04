import Langlands.Geometry.Analytic.SaturatedStrongComposition
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # The category of actual saturated affinoid atlas presentations -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : AffinoidAtlasPresentation.{u, v, w} K}

/-- With a source containing every local full domain, one admissible bounded
pullback per source chart detects the entire strong morphism. -/
theorem ext_of_saturated {f g : StrongHom A B}
    (ha : A.atlas.HasAllLocalDomains) (hb : f.baseMap = g.baseMap)
    (hp : ∀ i, ∃ (j : B.atlas.Index)
      (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      f.pullback i j h = g.pullback i j (by rw [← hb]; exact h)) :
    f = g := by
  rcases f with ⟨fb, ft, fp, fc, fr⟩
  rcases g with ⟨gb, gt, gp, gc, gr⟩
  dsimp only at hb hp ⊢
  subst gb
  refine StrongHom.ext (f := ⟨fb, ft, fp, fc, fr⟩)
    (g := ⟨fb, gt, gp, gc, gr⟩) rfl ?_
  apply heq_of_eq
  funext i k h
  obtain ⟨j, hj, heq⟩ := hp i
  have hf := (⟨fb, ft, fp, fc, fr⟩ : StrongHom A B).pullback_eq_changeTargetPullback
    ha i j k hj h
  have hg := (⟨fb, gt, gp, gc, gr⟩ : StrongHom A B).pullback_eq_changeTargetPullback
    ha i j k hj h
  dsimp only [changeTargetPullback] at hf hg
  exact hf.trans (by simpa only [heq] using hg.symm)

@[simp]
theorem id_saturatedComp (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) :
    (id A).saturatedComp f ha ha = f := by
  refine ext_of_saturated ha rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [saturatedComp_pullback (id A) f ha ha i i j
    (by simp only [id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf hf]
  change (A.atlas.restriction i i _).comp (f.pullback i j hf) = _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

@[simp]
theorem saturatedComp_id (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains) :
    f.saturatedComp (id B) ha hb = f := by
  refine ext_of_saturated ha rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [saturatedComp_pullback f (id B) ha hb i j j hf
    (by simp only [id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf]
  change (f.pullback i j hf).comp (B.atlas.restriction j j _) = _
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- Associativity retains every supplied bounded algebra map, including
pullbacks at targets unrelated to the charts used to compute the composite. -/
theorem saturatedComp_assoc (f : StrongHom A B) (g : StrongHom B C)
    (h : StrongHom C D) (ha : A.atlas.HasAllLocalDomains)
    (hb : B.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains) :
    (f.saturatedComp g ha hb).saturatedComp h ha hc =
      f.saturatedComp (g.saturatedComp h hb hc) ha hb := by
  refine ext_of_saturated ha rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨k, hg⟩ := g.target_exists j
  obtain ⟨l, hh⟩ := h.target_exists k
  have hfg := f.comp_admissible g i j k hf hg
  have hgh := g.comp_admissible h j k l hg hh
  have hfg_h := (f.saturatedComp g ha hb).comp_admissible h i k l hfg hh
  refine ⟨l, hfg_h, ?_⟩
  rw [saturatedComp_pullback (f.saturatedComp g ha hb) h ha hc i k l hfg hh hfg_h,
    saturatedComp_pullback f (g.saturatedComp h hb hc) ha hb i j l hf hgh]
  dsimp only [chainPullback]
  rw [saturatedComp_pullback f g ha hb i j k hf hg hfg,
    saturatedComp_pullback g h hb hc j k l hg hh hgh]
  exact BoundedAlgHom.comp_assoc _ _ _

/-- Where the earlier directed construction applies, the new composition
agrees with it on the entire original strong-map family. -/
theorem saturatedComp_eq_compOfDirected (f : StrongHom A B) (g : StrongHom B C)
    (ha : A.atlas.HasAllLocalDomains) (hb : B.atlas.HasAllLocalDomains)
    (hbd : B.atlas.HasDirectedCharts) (hcd : C.atlas.HasDirectedCharts) :
    f.saturatedComp g ha hb = f.compOfDirected g hbd hcd := by
  refine ext_of_saturated ha rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨k, hg⟩ := g.target_exists j
  have h := f.comp_admissible g i j k hf hg
  exact ⟨k, h, (f.saturatedComp_pullback g ha hb i j k hf hg h).trans
    (f.compOfDirected_pullback g hbd hcd i j k hf hg h).symm⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- An actual affinoid atlas presentation containing every local full
affinoid domain. The property is realized by the constructed saturation. -/
structure SaturatedAtlasPresentation (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] where
  presentation : AffinoidAtlasPresentation.{u, v, w} K
  hasAllLocalDomains : presentation.atlas.HasAllLocalDomains

namespace SaturatedAtlasPresentation

instance : Category (SaturatedAtlasPresentation.{u, v, w} K) where
  Hom A B := AffinoidAtlasPresentation.StrongHom A.presentation B.presentation
  id A := AffinoidAtlasPresentation.StrongHom.id A.presentation
  comp {A B _C} f g := f.saturatedComp g A.hasAllLocalDomains B.hasAllLocalDomains
  id_comp {A _B} f := f.id_saturatedComp A.hasAllLocalDomains
  comp_id {A B} f := f.saturatedComp_id A.hasAllLocalDomains B.hasAllLocalDomains
  assoc {A B C _D} f g h :=
    f.saturatedComp_assoc g h A.hasAllLocalDomains B.hasAllLocalDomains C.hasAllLocalDomains

@[simp]
theorem baseMap_id (A : SaturatedAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem baseMap_comp {A B C : SaturatedAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).baseMap = g.baseMap.comp f.baseMap := rfl

/-- Retain the literal spaces and continuous maps of saturated presentations. -/
def spaceFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤ TopCat.{v} where
  obj A := A.presentation.space
  map f := TopCat.ofHom f.baseMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every actual presentation supplies an object by the existing construction
on all local full domains, on exactly the original ambient space. -/
def ofSaturation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    SaturatedAtlasPresentation.{u, v, v} K where
  presentation := A.saturatedPresentation
  hasAllLocalDomains := A.atlas.saturatedAtlas_hasAllLocalDomains

@[simp]
theorem ofSaturation_space (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (ofSaturation A).presentation.space = A.space := rfl

end SaturatedAtlasPresentation

end Langlands.Analytic
