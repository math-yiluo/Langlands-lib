import Langlands.Geometry.Analytic.DisjointAffinoidAtlas

/-! # Componentwise bounded morphisms of actual disjoint affinoid families -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- A family of genuine finite positive-polyradius quotient presentations.
Its underlying space and atlas are constructed from this data. -/
structure AffinoidFamily where
  Index : Type v
  algebra : Index → PresentedAffinoidAlgebra K

namespace AffinoidFamily

variable {K}

/-- The actual disjoint sum of the spectra of the given quotient algebras. -/
abbrev Space (A : AffinoidFamily.{u, v} K) :=
  DisjointAffinoidAtlas.Space A.algebra

/-- The published constructed atlas on this family. -/
def atlas [CompleteSpace K] (A : AffinoidFamily.{u, v} K) :
    IndexedAffinoidAtlas.{u, max u v, v} K A.Space :=
  DisjointAffinoidAtlas.atlas A.algebra

/-- Componentwise morphisms retain an actual bounded pullback on each algebra.
The index map is chosen even on components with empty spectrum. -/
structure Hom (A B : AffinoidFamily.{u, v} K) where
  indexMap : A.Index → B.Index
  pullback : ∀ i, BoundedAlgHom K (B.algebra (indexMap i)) (A.algebra i)

namespace Hom

variable {A B C : AffinoidFamily.{u, v} K}

@[ext]
theorem ext {f g : Hom A B} (hi : f.indexMap = g.indexMap)
    (hp : HEq f.pullback g.pullback) : f = g := by
  cases f
  cases g
  cases hi
  cases eq_of_heq hp
  rfl

/-- Pull back along the bounded component algebra map, then include the
resulting spectrum point in its chosen target component. -/
def spectrumMap (f : Hom A B) : C(A.Space, B.Space) where
  toFun x := ⟨f.indexMap x.fst, BanachSpectrum.comap
    (f.pullback x.fst).toBoundedRingHom x.snd⟩
  continuous_toFun := continuous_sigma fun i =>
    (continuous_sigmaMk
      (σ := fun j : B.Index => BanachSpectrum (B.algebra j))
      (i := f.indexMap i)).comp
      (BanachSpectrum.comapContinuous (f.pullback i).toBoundedRingHom).continuous

@[simp]
theorem spectrumMap_fst (f : Hom A B) (x : A.Space) :
    (f.spectrumMap x).fst = f.indexMap x.fst := rfl

end Hom

instance : Category (AffinoidFamily.{u, v} K) where
  Hom := Hom
  id A := ⟨id, fun i => BoundedAlgHom.id K (A.algebra i)⟩
  comp f g := ⟨g.indexMap ∘ f.indexMap,
    fun i => (f.pullback i).comp (g.pullback (f.indexMap i))⟩
  id_comp _ := Hom.ext rfl (heq_of_eq (funext fun _ =>
    BoundedAlgHom.ext fun _ => rfl))
  comp_id _ := Hom.ext rfl (heq_of_eq (funext fun _ =>
    BoundedAlgHom.ext fun _ => rfl))
  assoc _ _ _ := Hom.ext rfl (heq_of_eq (funext fun _ =>
    BoundedAlgHom.ext fun _ => rfl))

namespace Hom

variable {A B C : AffinoidFamily.{u, v} K}

@[simp]
theorem indexMap_id (A : AffinoidFamily.{u, v} K) :
    (𝟙 A : A ⟶ A).indexMap = id := rfl

@[simp]
theorem pullback_id (A : AffinoidFamily.{u, v} K) (i : A.Index) :
    (𝟙 A : A ⟶ A).pullback i = BoundedAlgHom.id K (A.algebra i) := rfl

@[simp]
theorem indexMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).indexMap = g.indexMap ∘ f.indexMap := rfl

@[simp]
theorem pullback_comp (f : A ⟶ B) (g : B ⟶ C) (i : A.Index) :
    (f ≫ g).pullback i = (f.pullback i).comp (g.pullback (f.indexMap i)) := rfl

theorem spectrumMap_id (A : AffinoidFamily.{u, v} K) :
    (𝟙 A : A ⟶ A).spectrumMap = ContinuousMap.id A.Space := by
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  congr 1

theorem spectrumMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).spectrumMap = g.spectrumMap.comp f.spectrumMap := by
  apply ContinuousMap.ext
  rintro ⟨i, x⟩
  congr 1

/-- A nonempty source component has a nonempty chosen target component:
its seminorm pulls back along the actual bounded algebra map. -/
def chartTarget (f : A ⟶ B) (c : DisjointAffinoidAtlas.ChartIndex A.algebra) :
    DisjointAffinoidAtlas.ChartIndex B.algebra :=
  ⟨f.indexMap c.val, c.property.elim fun x =>
    ⟨BanachSpectrum.comap (f.pullback c.val).toBoundedRingHom x⟩⟩

@[simp]
theorem chartTarget_id (A : AffinoidFamily.{u, v} K)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra) :
    (𝟙 A : A ⟶ A).chartTarget c = c := rfl

@[simp]
theorem chartTarget_comp (f : A ⟶ B) (g : B ⟶ C)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra) :
    (f ≫ g).chartTarget c = g.chartTarget (f.chartTarget c) := rfl

theorem spectrumMap_chart (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (x : BanachSpectrum (DisjointAffinoidAtlas.chartAlgebra A.algebra c)) :
    f.spectrumMap (DisjointAffinoidAtlas.chart A.algebra c x) =
      DisjointAffinoidAtlas.chart B.algebra (f.chartTarget c)
        (BanachSpectrum.comap (f.pullback c.val).toBoundedRingHom x) := rfl

/-- The image of every chart lies in an actual target chart. -/
theorem image_chart_subset (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra) :
    f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra (f.chartTarget c) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (f.pullback c.val).toBoundedRingHom x, rfl⟩

/-- A target chart containing the image of a nonempty source chart must be
the chosen target component. This uses points only to identify indices. -/
theorem chartTarget_eq (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (d : DisjointAffinoidAtlas.ChartIndex B.algebra)
    (h : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d) :
    f.chartTarget c = d := by
  obtain ⟨x⟩ := c.property
  exact DisjointAffinoidAtlas.chart_eq_of_mem_inter B.algebra
    (f.chartTarget c) d
    ⟨BanachSpectrum.comap (f.pullback c.val).toBoundedRingHom x, rfl⟩
    (h ⟨_, ⟨x, rfl⟩, rfl⟩)

/-- For every chart pair satisfying the image containment, transport the
original bounded pullback along the forced equality of target indices. -/
def localPullback (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (d : DisjointAffinoidAtlas.ChartIndex B.algebra)
    (h : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d) :
    BoundedAlgHom K (DisjointAffinoidAtlas.chartAlgebra B.algebra d)
      (DisjointAffinoidAtlas.chartAlgebra A.algebra c) := by
  have hd := f.chartTarget_eq c d h
  subst d
  exact f.pullback c.val

/-- In the chosen target component, the local map is the original algebra map. -/
theorem localPullback_target (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (h : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra (f.chartTarget c)) :
    f.localPullback c (f.chartTarget c) h = f.pullback c.val := rfl

theorem localPullback_chart (f : A ⟶ B)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (d : DisjointAffinoidAtlas.ChartIndex B.algebra)
    (h : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d)
    (x : BanachSpectrum (DisjointAffinoidAtlas.chartAlgebra A.algebra c)) :
    DisjointAffinoidAtlas.chart B.algebra d
      (BanachSpectrum.comap (f.localPullback c d h).toBoundedRingHom x) =
      f.spectrumMap (DisjointAffinoidAtlas.chart A.algebra c x) := by
  have hd := f.chartTarget_eq c d h
  subst d
  rfl

/-- Compatibility with both source and target atlas restrictions is an
equality of bounded algebra maps, preserving nonreduced algebra data. -/
theorem localPullback_naturality (f : A ⟶ B)
    (c c' : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (d d' : DisjointAffinoidAtlas.ChartIndex B.algebra)
    (hcc' : DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain A.algebra c')
    (hdd' : DisjointAffinoidAtlas.chartDomain B.algebra d ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d')
    (h : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d)
    (h' : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c' ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d') :
    (DisjointAffinoidAtlas.restriction A.algebra c c' hcc').comp
        (f.localPullback c' d' h') =
      (f.localPullback c d h).comp
        (DisjointAffinoidAtlas.restriction B.algebra d d' hdd') := by
  have hc := DisjointAffinoidAtlas.chart_eq_of_subset A.algebra c c' hcc'
  have hd := DisjointAffinoidAtlas.chart_eq_of_subset B.algebra d d' hdd'
  subst c'
  subst d'
  exact BoundedAlgHom.ext fun _ => rfl

/-- The categorical identity has the actual bounded identity as its local map. -/
theorem localPullback_id (A : AffinoidFamily.{u, v} K)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (h : (𝟙 A : A ⟶ A).spectrumMap ''
      DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
        DisjointAffinoidAtlas.chartDomain A.algebra c) :
    (𝟙 A : A ⟶ A).localPullback c c h =
      BoundedAlgHom.id K (DisjointAffinoidAtlas.chartAlgebra A.algebra c) := rfl

/-- Composition agrees with contravariant composition of the local bounded
maps for every compatible triple of source, intermediate and target charts. -/
theorem localPullback_comp (f : A ⟶ B) (g : B ⟶ C)
    (c : DisjointAffinoidAtlas.ChartIndex A.algebra)
    (d : DisjointAffinoidAtlas.ChartIndex B.algebra)
    (e : DisjointAffinoidAtlas.ChartIndex C.algebra)
    (hfd : f.spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain B.algebra d)
    (hge : g.spectrumMap '' DisjointAffinoidAtlas.chartDomain B.algebra d ⊆
      DisjointAffinoidAtlas.chartDomain C.algebra e)
    (hfe : (f ≫ g).spectrumMap '' DisjointAffinoidAtlas.chartDomain A.algebra c ⊆
      DisjointAffinoidAtlas.chartDomain C.algebra e) :
    (f ≫ g).localPullback c e hfe =
      (f.localPullback c d hfd).comp (g.localPullback d e hge) := by
  have hd := f.chartTarget_eq c d hfd
  subst d
  have he := g.chartTarget_eq (f.chartTarget c) e hge
  subst e
  rfl

end Hom

/-- The actual topological spectrum realization of the componentwise bounded
category. No algebra maps are identified using spectral-point equality. -/
def spectrumFunctor : AffinoidFamily.{u, v} K ⥤ TopCat.{max u v} where
  obj A := TopCat.of A.Space
  map f := TopCat.ofHom f.spectrumMap
  map_id A := congrArg TopCat.ofHom (Hom.spectrumMap_id A)
  map_comp f g := congrArg TopCat.ofHom (Hom.spectrumMap_comp f g)

end AffinoidFamily

end Langlands.Analytic
