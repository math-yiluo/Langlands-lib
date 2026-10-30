import Langlands.Geometry.Analytic.DisjointAffinoidMorphisms
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Bounded morphisms with monotone chosen atlas charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Topology

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Domain factorization uniqueness detects equality of bounded maps after
precomposition with an atlas restriction; no point-separation assertion is used. -/
theorem restriction_hom_ext (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (R : PresentedAffinoidAlgebra K) (ψ χ : BoundedAlgHom K (a.algebra i) R)
    (heq : ψ.comp (a.restriction i j h) = χ.comp (a.restriction i j h)) : ψ = χ := by
  have hφ : ∀ x : BanachSpectrum R,
      a.chart j (BanachSpectrum.comap
        (ψ.comp (a.restriction i j h)).toBoundedRingHom x) ∈ Set.range (a.chart i) := by
    intro x
    change a.chart j (BanachSpectrum.comap (a.restriction i j h).toBoundedRingHom
      (BanachSpectrum.comap ψ.toBoundedRingHom x)) ∈ Set.range (a.chart i)
    rw [a.restriction_chart]
    exact ⟨_, rfl⟩
  exact (a.restriction_universal i j h R _ hφ).unique rfl heq.symm

end IndexedAffinoidAtlas

/-- A supplied indexed atlas on its actual topological space. This is
presentation data; no extended atlas or localization is constructed here. -/
structure AffinoidAtlasPresentation (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] where
  space : TopCat.{v}
  atlas : IndexedAffinoidAtlas.{u, v, w} K space

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A bounded map with a monotone chosen target for each source chart.
Restriction compatibility is equality of bounded algebra maps. -/
structure Hom (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  baseMap : C(A.space, B.space)
  indexMap : A.atlas.Index → B.atlas.Index
  index_mono : ∀ i j, Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart j) →
    Set.range (B.atlas.chart (indexMap i)) ⊆ Set.range (B.atlas.chart (indexMap j))
  pullback : ∀ i, BoundedAlgHom K (B.atlas.algebra (indexMap i)) (A.atlas.algebra i)
  chart_comm : ∀ i (x : BanachSpectrum (A.atlas.algebra i)),
    B.atlas.chart (indexMap i) (BanachSpectrum.comap (pullback i).toBoundedRingHom x) =
      baseMap (A.atlas.chart i x)
  restriction_comm : ∀ i j h,
    (A.atlas.restriction i j h).comp (pullback j) =
      (pullback i).comp (B.atlas.restriction (indexMap i) (indexMap j) (index_mono i j h))

namespace Hom

variable {A B C D : AffinoidAtlasPresentation.{u, v, w} K}

@[ext]
theorem ext {f g : Hom A B} (hb : f.baseMap = g.baseMap)
    (hi : f.indexMap = g.indexMap) (hp : HEq f.pullback g.pullback) : f = g := by
  cases f
  cases g
  cases hb
  cases hi
  cases eq_of_heq hp
  rfl

/-- The underlying map sends each chart into the chosen target chart. -/
theorem image_chart_subset (f : Hom A B) (i : A.atlas.Index) :
    f.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (B.atlas.chart (f.indexMap i)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (f.pullback i).toBoundedRingHom x, f.chart_comm i x⟩

/-- If an admissible target chart lies inside the selected target, its
bounded pullback is constructed by the atlas domain universal property. -/
theorem localPullback_existsUnique (f : Hom A B) (i : A.atlas.Index)
    (j : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    ∃! ψ : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i),
      ψ.comp (B.atlas.restriction j (f.indexMap i) hj) = f.pullback i := by
  apply B.atlas.restriction_universal j (f.indexMap i) hj (A.atlas.algebra i)
  intro x
  rw [f.chart_comm]
  exact hf ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The unique actual bounded factorization to this smaller target chart. -/
def localPullback (f : Hom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) :=
  Classical.choose (f.localPullback_existsUnique i j hj hf).exists

theorem localPullback_comp_restriction (f : Hom A B) (i : A.atlas.Index)
    (j : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    (f.localPullback i j hj hf).comp (B.atlas.restriction j (f.indexMap i) hj) =
      f.pullback i :=
  Classical.choose_spec (f.localPullback_existsUnique i j hj hf).exists

theorem localPullback_unique (f : Hom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (ψ : BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i))
    (hψ : ψ.comp (B.atlas.restriction j (f.indexMap i) hj) = f.pullback i) :
    ψ = f.localPullback i j hj hf :=
  (f.localPullback_existsUnique i j hj hf).unique hψ
    (f.localPullback_comp_restriction i j hj hf)

/-- The factorization has exactly the given underlying map in chart coordinates. -/
theorem localPullback_chart (f : Hom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart j (BanachSpectrum.comap (f.localPullback i j hj hf).toBoundedRingHom x) =
      f.baseMap (A.atlas.chart i x) := by
  rw [← f.chart_comm i x, ← f.localPullback_comp_restriction i j hj hf]
  exact (B.atlas.restriction_chart j (f.indexMap i) hj _).symm

/-- At the selected target the factorization recovers the original pullback. -/
theorem localPullback_target (f : Hom A B) (i : A.atlas.Index)
    (hj : Set.range (B.atlas.chart (f.indexMap i)) ⊆
      Set.range (B.atlas.chart (f.indexMap i)))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (B.atlas.chart (f.indexMap i))) :
    f.localPullback i (f.indexMap i) hj hf = f.pullback i := by
  simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
    f.localPullback_comp_restriction i (f.indexMap i) hj hf

/-- Smaller-target pullbacks commute with both atlas restrictions as bounded
algebra maps, using the proved uniqueness of domain factorizations. -/
theorem localPullback_naturality (f : Hom A B)
    (i i' : A.atlas.Index) (j j' : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hjj' : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart (f.indexMap i)))
    (hj' : Set.range (B.atlas.chart j') ⊆ Set.range (B.atlas.chart (f.indexMap i')))
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hf' : f.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')) :
    (A.atlas.restriction i i' hi).comp (f.localPullback i' j' hj' hf') =
      (f.localPullback i j hj hf).comp (B.atlas.restriction j j' hjj') := by
  apply B.atlas.restriction_hom_ext j' (f.indexMap i') hj' (A.atlas.algebra i)
  have hjt := hj.trans (f.index_mono i i' hi)
  calc
    ((A.atlas.restriction i i' hi).comp (f.localPullback i' j' hj' hf')).comp
        (B.atlas.restriction j' (f.indexMap i') hj') =
        (A.atlas.restriction i i' hi).comp (f.pullback i') := by
      rw [BoundedAlgHom.comp_assoc, f.localPullback_comp_restriction]
    _ = (f.pullback i).comp
        (B.atlas.restriction (f.indexMap i) (f.indexMap i') (f.index_mono i i' hi)) :=
      f.restriction_comm i i' hi
    _ = ((f.localPullback i j hj hf).comp
        (B.atlas.restriction j (f.indexMap i) hj)).comp
        (B.atlas.restriction (f.indexMap i) (f.indexMap i') (f.index_mono i i' hi)) := by
      rw [f.localPullback_comp_restriction]
    _ = (f.localPullback i j hj hf).comp
        (B.atlas.restriction j (f.indexMap i') hjt) := by
      rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]
    _ = ((f.localPullback i j hj hf).comp (B.atlas.restriction j j' hjj')).comp
        (B.atlas.restriction j' (f.indexMap i') hj') := by
      rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]

/-- Identity retains the actual bounded identity on every chart algebra. -/
def id (A : AffinoidAtlasPresentation.{u, v, w} K) : Hom A A where
  baseMap := ContinuousMap.id A.space
  indexMap := _root_.id
  index_mono _ _ h := h
  pullback i := BoundedAlgHom.id K (A.atlas.algebra i)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

/-- Composition retains the selected intermediate chart and composes its
bounded pullbacks in the contravariant order. -/
def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  baseMap := g.baseMap.comp f.baseMap
  indexMap := g.indexMap ∘ f.indexMap
  index_mono i j h := g.index_mono _ _ (f.index_mono i j h)
  pullback i := (f.pullback i).comp (g.pullback (f.indexMap i))
  chart_comm i x := by
    change C.atlas.chart (g.indexMap (f.indexMap i))
      (BanachSpectrum.comap (g.pullback (f.indexMap i)).toBoundedRingHom
        (BanachSpectrum.comap (f.pullback i).toBoundedRingHom x)) = _
    rw [g.chart_comm, f.chart_comm]
    rfl
  restriction_comm i j h := by
    change (A.atlas.restriction i j h).comp
      ((f.pullback j).comp (g.pullback (f.indexMap j))) =
      ((f.pullback i).comp (g.pullback (f.indexMap i))).comp _
    rw [← BoundedAlgHom.comp_assoc, f.restriction_comm,
      BoundedAlgHom.comp_assoc, g.restriction_comm, ← BoundedAlgHom.comp_assoc]
    rfl

end Hom

instance : Category (AffinoidAtlasPresentation.{u, v, w} K) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))
  comp_id _ := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))
  assoc _ _ _ := Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

namespace Hom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

@[simp]
theorem baseMap_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).baseMap = ContinuousMap.id A.space := rfl

@[simp]
theorem indexMap_id (A : AffinoidAtlasPresentation.{u, v, w} K) :
    (𝟙 A : A ⟶ A).indexMap = _root_.id := rfl

@[simp]
theorem pullback_id (A : AffinoidAtlasPresentation.{u, v, w} K) (i : A.atlas.Index) :
    (𝟙 A : A ⟶ A).pullback i = BoundedAlgHom.id K (A.atlas.algebra i) := rfl

@[simp]
theorem baseMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).baseMap = g.baseMap.comp f.baseMap := rfl

@[simp]
theorem indexMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).indexMap = g.indexMap ∘ f.indexMap := rfl

@[simp]
theorem pullback_comp (f : A ⟶ B) (g : B ⟶ C) (i : A.atlas.Index) :
    (f ≫ g).pullback i = (f.pullback i).comp (g.pullback (f.indexMap i)) := rfl

end Hom

/-- Forget the chosen atlas maps, retaining their actual continuous maps. -/
def spaceFunctor : AffinoidAtlasPresentation.{u, v, w} K ⥤ TopCat.{v} where
  obj A := A.space
  map f := TopCat.ofHom f.baseMap
  map_id _ := rfl
  map_comp _ _ := rfl

end AffinoidAtlasPresentation

namespace AffinoidFamily

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The already constructed disjoint atlas, bundled as presentation data. -/
def atlasPresentation (A : AffinoidFamily.{u, v} K) :
    AffinoidAtlasPresentation.{u, max u v, v} K where
  space := TopCat.of A.Space
  atlas := A.atlas

namespace Hom

variable {A B C : AffinoidFamily.{u, v} K}

/-- A componentwise bounded map supplies actual monotone chosen atlas data. -/
def atlasMap (f : A ⟶ B) : A.atlasPresentation ⟶ B.atlasPresentation where
  baseMap := f.spectrumMap
  indexMap := f.chartTarget
  index_mono i j h := by
    have hij := DisjointAffinoidAtlas.chart_eq_of_subset A.algebra i j h
    subst j
    exact Subset.rfl
  pullback i := f.pullback i.val
  chart_comm _ _ := rfl
  restriction_comm i j h := by
    have hij := DisjointAffinoidAtlas.chart_eq_of_subset A.algebra i j h
    subst j
    rfl

@[simp]
theorem atlasMap_id (A : AffinoidFamily.{u, v} K) :
    (𝟙 A : A ⟶ A).atlasMap = 𝟙 A.atlasPresentation :=
  AffinoidAtlasPresentation.Hom.ext (spectrumMap_id A) rfl (heq_of_eq rfl)

theorem atlasMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).atlasMap = f.atlasMap ≫ g.atlasMap :=
  AffinoidAtlasPresentation.Hom.ext (f.spectrumMap_comp g) rfl (heq_of_eq rfl)

end Hom

/-- Concrete realization of disjoint affinoid families in the category of
monotone chosen atlas maps. -/
def atlasFunctor : AffinoidFamily.{u, v} K ⥤
    AffinoidAtlasPresentation.{u, max u v, v} K where
  obj := atlasPresentation
  map := Hom.atlasMap
  map_id := Hom.atlasMap_id
  map_comp := Hom.atlasMap_comp

/-- The atlas construction retains the published spectrum diagram exactly. -/
theorem atlasFunctor_spaceFunctor :
    atlasFunctor (K := K) ⋙ AffinoidAtlasPresentation.spaceFunctor = spectrumFunctor := rfl

end AffinoidFamily

end Langlands.Analytic
