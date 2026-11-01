import Langlands.Geometry.Analytic.AtlasSubatlas
import Mathlib.CategoryTheory.Action.Basic

/-! # Removing empty charts without changing the underlying space -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open Set Topology CategoryTheory
open scoped Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A condition on an original chart, with no replacement of its algebra. -/
def NonemptyChart (i : a.Index) : Prop := Nonempty (BanachSpectrum (a.algebra i))

/-- Empty spaces may satisfy this condition by having no charts. -/
def HasNonemptyCharts : Prop := ∀ i, a.NonemptyChart i

/-- A point in an original chart already witnesses that chart's survival. -/
theorem nonemptyCharts_locallyRefining :
    a.IsLocallyRefiningSelection a.NonemptyChart := by
  rintro U ⟨i, rfl⟩ x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨{Set.range (a.chart i)}, Set.finite_singleton _, ?_, ?_, ?_⟩
  · exact Set.singleton_subset_iff.mpr ⟨⟨i, ⟨y⟩⟩, rfl⟩
  · intro V hV
    rcases Set.mem_singleton_iff.mp hV with rfl
    exact ⟨Subset.rfl, y, hy⟩
  · simpa only [Set.sUnion_singleton] using
      (self_mem_nhdsWithin : Set.range (a.chart i) ∈ 𝓝[Set.range (a.chart i)] x)

/-- The actual same-space subatlas of all original nonempty-spectrum charts. -/
def nonemptySubatlas : IndexedAffinoidAtlas.{u, v, w} K X :=
  a.subatlas a.NonemptyChart a.nonemptyCharts_locallyRefining

theorem nonemptySubatlas_hasNonemptyCharts : a.nonemptySubatlas.HasNonemptyCharts :=
  fun i => i.property

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Delete only empty-spectrum charts, retaining the original space. -/
def nonemptyPresentation (A : AffinoidAtlasPresentation.{u, v, w} K) :
    AffinoidAtlasPresentation.{u, v, w} K :=
  A.subpresentation A.atlas.NonemptyChart A.atlas.nonemptyCharts_locallyRefining

/-- The canonical identity-on-space inclusion with original bounded identities. -/
def nonemptyInclusion (A : AffinoidAtlasPresentation.{u, v, w} K) :
    A.nonemptyPresentation ⟶ A :=
  A.subatlasInclusion A.atlas.NonemptyChart A.atlas.nonemptyCharts_locallyRefining

namespace Hom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- The actual bounded pullback sends a source spectrum point to a target point. -/
theorem nonemptyChart_target (f : A ⟶ B) (i : A.atlas.Index)
    (hi : A.atlas.NonemptyChart i) : B.atlas.NonemptyChart (f.indexMap i) := by
  obtain ⟨x⟩ := hi
  exact ⟨BanachSpectrum.comap (f.pullback i).toBoundedRingHom x⟩

/-- Restrict the original complete arrow to both nonempty-chart subatlases. -/
def nonemptyMap (f : A ⟶ B) : A.nonemptyPresentation ⟶ B.nonemptyPresentation where
  baseMap := f.baseMap
  indexMap i := ⟨f.indexMap i.val, f.nonemptyChart_target i.val i.property⟩
  index_mono i j h := f.index_mono i.val j.val h
  pullback i := f.pullback i.val
  chart_comm i x := f.chart_comm i.val x
  restriction_comm i j h := f.restriction_comm i.val j.val h

@[simp]
theorem nonemptyMap_baseMap (f : A ⟶ B) :
    f.nonemptyMap.baseMap = f.baseMap := rfl

@[simp]
theorem nonemptyMap_indexMap_val (f : A ⟶ B)
    (i : A.nonemptyPresentation.atlas.Index) :
    (f.nonemptyMap.indexMap i).val = f.indexMap i.val := rfl

@[simp]
theorem nonemptyMap_pullback (f : A ⟶ B)
    (i : A.nonemptyPresentation.atlas.Index) :
    f.nonemptyMap.pullback i = f.pullback i.val := rfl

@[simp]
theorem nonemptyMap_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).nonemptyMap = 𝟙 A.nonemptyPresentation :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

theorem nonemptyMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).nonemptyMap = f.nonemptyMap ≫ g.nonemptyMap :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- The inclusion is natural for the complete bounded maps. -/
theorem nonemptyMap_nonemptyInclusion (f : A ⟶ B) :
    f.nonemptyMap ≫ B.nonemptyInclusion = A.nonemptyInclusion ≫ f :=
  ext rfl rfl (heq_of_eq (funext fun _ => rfl))

end Hom

/-- An actual endofunctor on presentations and their complete chosen maps. -/
def nonemptyFunctor : AffinoidAtlasPresentation.{u, v, w} K ⥤
    AffinoidAtlasPresentation.{u, v, w} K where
  obj := nonemptyPresentation
  map := Hom.nonemptyMap
  map_id := Hom.nonemptyMap_id
  map_comp := Hom.nonemptyMap_comp

/-- The identity-on-space inclusions form a natural transformation. -/
def nonemptyInclusionNat : nonemptyFunctor (K := K) ⟶ 𝟭 _ where
  app := nonemptyInclusion
  naturality _ _ f := f.nonemptyMap_nonemptyInclusion

/-- Underlying continuous spaces and maps are retained exactly. -/
theorem nonemptyFunctor_spaceFunctor :
    nonemptyFunctor (K := K) ⋙ spaceFunctor = spaceFunctor := rfl

/-- An inverse inclusion exists when all original charts already survive. -/
def nonemptyInv (A : AffinoidAtlasPresentation.{u, v, w} K)
    (h : A.atlas.HasNonemptyCharts) : A ⟶ A.nonemptyPresentation where
  baseMap := ContinuousMap.id A.space
  indexMap i := ⟨i, h i⟩
  index_mono _ _ hi := hi
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- No deletion of chart data occurs under this explicit hypothesis. -/
def nonemptyIso (A : AffinoidAtlasPresentation.{u, v, w} K)
    (h : A.atlas.HasNonemptyCharts) : A.nonemptyPresentation ≅ A where
  hom := A.nonemptyInclusion
  inv := A.nonemptyInv h
  hom_inv_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))
  inv_hom_id := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Every actual categorical monoid action restricts to the retained charts. -/
def nonemptyActionFunctor (M : Type z) [Monoid M] :
    Action (AffinoidAtlasPresentation.{u, v, w} K) M ⥤
      Action (AffinoidAtlasPresentation.{u, v, w} K) M :=
  nonemptyFunctor.mapAction M

/-- The canonical inclusion is equivariant for the original action. -/
def nonemptyActionInclusion {M : Type z} [Monoid M]
    (A : Action (AffinoidAtlasPresentation.{u, v, w} K) M) :
    (nonemptyActionFunctor M).obj A ⟶ A where
  hom := A.V.nonemptyInclusion
  comm m := (A.ρ m).nonemptyMap_nonemptyInclusion

end AffinoidAtlasPresentation

end Langlands.Analytic
