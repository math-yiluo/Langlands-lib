import Langlands.Geometry.Analytic.CoherentStrongComposition
import Langlands.Geometry.Analytic.SaturatedStrongCategory

/-! # The category of actual original compatible strong atlas maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C D : AffinoidAtlasPresentation.{u, v, w} K}

/-- One complete admissible bounded pullback per source chart detects a
compatible strong map; all the other pullbacks follow by bounded chart change. -/
theorem ext_of_pullback {f g : CompatibleStrongHom A B}
    (hb : f.baseMap = g.baseMap)
    (hp : ∀ i, ∃ (j : B.atlas.Index)
      (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      f.pullback i j h = g.pullback i j (by rw [← hb]; exact h)) :
    f = g :=
  ext (StrongHom.ext_of_coherent f.coherent g.coherent hb hp)

@[simp]
theorem id_comp (f : CompatibleStrongHom A B) : (id A).comp f = f := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [comp_pullback (id A) f i i j
    (by simp only [id, StrongHom.id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf hf]
  change (A.atlas.restriction i i _).comp (f.pullback i j hf) = _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

@[simp]
theorem comp_id (f : CompatibleStrongHom A B) : f.comp (id B) = f := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  refine ⟨j, hf, ?_⟩
  rw [comp_pullback f (id B) i j j hf
    (by simp only [id, StrongHom.id, ContinuousMap.coe_id, Set.image_id, Subset.rfl]) hf]
  change (f.pullback i j hf).comp (B.atlas.restriction j j _) = _
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]

/-- Associativity is equality of all original bounded pullbacks, proved
by recovery of one admissible chain and then full coherent extensionality. -/
theorem comp_assoc (f : CompatibleStrongHom A B) (g : CompatibleStrongHom B C)
    (h : CompatibleStrongHom C D) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  obtain ⟨k, hg⟩ := g.target_exists j
  obtain ⟨l, hh⟩ := h.target_exists k
  have hfg := f.toStrongHom.comp_admissible g.toStrongHom i j k hf hg
  have hgh := g.toStrongHom.comp_admissible h.toStrongHom j k l hg hh
  have hfg_h := (f.comp g).toStrongHom.comp_admissible h.toStrongHom i k l hfg hh
  refine ⟨l, hfg_h, ?_⟩
  rw [comp_pullback (f.comp g) h i k l hfg hh hfg_h,
    comp_pullback f (g.comp h) i j l hf hgh,
    comp_pullback f g i j k hf hg hfg,
    comp_pullback g h j k l hg hh hgh]
  exact BoundedAlgHom.comp_assoc _ _ _

end Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom

namespace Langlands.Analytic

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The actual original affinoid atlas presentations, with their category of
all-admissible compatible strong maps. The wrapper separates this category
from the existing category with monotone chosen target charts. -/
structure CompatibleAtlasPresentation (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] where
  presentation : AffinoidAtlasPresentation.{u, v, w} K

namespace CompatibleAtlasPresentation

instance : Category (CompatibleAtlasPresentation.{u, v, w} K) where
  Hom A B := AffinoidAtlasPresentation.CompatibleStrongHom A.presentation B.presentation
  id A := AffinoidAtlasPresentation.CompatibleStrongHom.id A.presentation
  comp f g := f.comp g
  id_comp f := f.id_comp
  comp_id f := f.comp_id
  assoc f g h := f.comp_assoc g h

@[simp]
theorem baseMap_id (A : CompatibleAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).baseMap = ContinuousMap.id A.presentation.space := rfl

@[simp]
theorem baseMap_comp {A B C : CompatibleAtlasPresentation.{u, v, w} K}
    (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).baseMap = g.baseMap.comp f.baseMap := rfl

/-- Retain exactly the actual ambient spaces and supplied continuous maps. -/
def spaceFunctor : CompatibleAtlasPresentation.{u, v, w} K ⥤ TopCat.{v} where
  obj A := A.presentation.space
  map f := TopCat.ofHom f.baseMap
  map_id _ := rfl
  map_comp _ _ := rfl

end CompatibleAtlasPresentation

namespace SaturatedAtlasPresentation

/-- Inclusion of the existing actual saturated category into the original
compatible category. Saturation proves compatibility of every strong map. -/
def compatibleFunctor : SaturatedAtlasPresentation.{u, v, w} K ⥤
    CompatibleAtlasPresentation.{u, v, w} K where
  obj A := ⟨A.presentation⟩
  map {A _B} f := AffinoidAtlasPresentation.CompatibleStrongHom.ofSaturated
    f A.hasAllLocalDomains
  map_id _ := AffinoidAtlasPresentation.CompatibleStrongHom.ext rfl
  map_comp _ _ := AffinoidAtlasPresentation.CompatibleStrongHom.ext rfl

/-- The inclusion changes neither the actual spaces nor their continuous maps. -/
theorem compatibleFunctor_spaceFunctor :
    compatibleFunctor (K := K) ⋙ CompatibleAtlasPresentation.spaceFunctor =
      spaceFunctor := rfl

instance : (compatibleFunctor (K := K) :
    SaturatedAtlasPresentation.{u, v, w} K ⥤ _).Faithful where
  map_injective h := congrArg
    AffinoidAtlasPresentation.CompatibleStrongHom.toStrongHom h

instance : (compatibleFunctor (K := K) :
    SaturatedAtlasPresentation.{u, v, w} K ⥤ _).Full where
  map_surjective f := ⟨f.toStrongHom, AffinoidAtlasPresentation.CompatibleStrongHom.ext rfl⟩

end SaturatedAtlasPresentation
end Langlands.Analytic
