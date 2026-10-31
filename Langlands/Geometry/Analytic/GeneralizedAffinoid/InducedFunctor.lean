import Langlands.Geometry.Analytic.GeneralizedAffinoid.InducedAction
import Langlands.Geometry.Analytic.StrongAtlasMaps

/-! # Functorial induction of actual positive-polyradius affinoid actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] [TopologicalSpace G] (H : Subgroup G)

/-- The original bounded pullback on every same-coset component. -/
def familyMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    family H X.unop ⟶ family H Y.unop where
  indexMap := id
  pullback _ := NormContinuousAction.homMap f.unop

@[simp]
theorem familyMap_pullback {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : G ⧸ H) :
    (familyMap H f).pullback c = NormContinuousAction.homMap f.unop := rfl

theorem familyMap_comm {X Y : NormContinuousSpace K H} (f : X ⟶ Y) (g : G) :
    actionMap H X.unop g ≫ familyMap H f =
      familyMap H f ≫ actionMap H Y.unop g := by
  apply AffinoidFamily.Hom.ext
    (f := actionMap H X.unop g ≫ familyMap H f)
    (g := familyMap H f ≫ actionMap H Y.unop g) rfl
  apply heq_of_eq
  funext c
  change G ⧸ H at c
  apply BoundedAlgHom.ext
  intro a
  change (X.unop.actionAut (correction H g c)).inv.toAlgHom
      (NormContinuousAction.homMap f.unop a) =
    NormContinuousAction.homMap f.unop
      ((Y.unop.actionAut (correction H g c)).inv.toAlgHom a)
  exact (NormContinuousAction.homMap_apply_action f.unop (correction H g c)⁻¹ a).symm

@[simp]
theorem familyMap_id (X : NormContinuousSpace K H) :
    familyMap H (𝟙 X) = 𝟙 (family H X.unop) := by
  apply AffinoidFamily.Hom.ext rfl
  exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)

theorem familyMap_comp {X Y Z : NormContinuousSpace K H}
    (f : X ⟶ Y) (k : Y ⟶ Z) :
    familyMap H (f ≫ k) = familyMap H f ≫ familyMap H k := by
  apply AffinoidFamily.Hom.ext rfl
  exact heq_of_eq (funext fun _ => BoundedAlgHom.ext fun _ => rfl)

/-- Geometric equivariant bounded maps induce actual equivariant family maps. -/
def functor : NormContinuousSpace K H ⥤ Action (AffinoidFamily.{u, v} K) G where
  obj X := action H X.unop
  map f := ⟨familyMap H f, familyMap_comm H f⟩
  map_id X := Action.Hom.ext (familyMap_id H X)
  map_comp f k := Action.Hom.ext (familyMap_comp H f k)

variable [IsTopologicalGroup G]

/-- The continuous spectrum realization of the bounded induction functor. -/
def spectrumFunctor (hH : IsOpen (H : Set G)) :
    NormContinuousSpace K H ⥤ ContAction TopCat.{max u v} G :=
  (Action.isContinuous TopCat G).lift
    (functor H ⋙ (AffinoidFamily.spectrumFunctor (K := K)).mapAction G)
    (fun X => (continuousSpectrum H X.unop hH).property)

/-- The actual balanced quotient with the already constructed quotient action. -/
def balancedAction (X : NormContinuousSpace K H) :
    ContAction TopCat.{max u v} G :=
  ⟨{ V := TopCat.of (Spectrum H X.unop)
     ρ :=
       { toFun := fun g => TopCat.ofHom ⟨(g • ·), continuous_const_smul g⟩
         map_one' := by
           apply TopCat.ext
           intro z
           exact one_smul G z
         map_mul' := by
           intro g k
           apply TopCat.ext
           intro z
           exact mul_smul g k z } },
   (Action.isContinuous_def _).mpr (by
     change Continuous (fun p : G × Spectrum H X.unop => p.1 • p.2)
     exact continuous_smul)⟩

/-- The original equivariant spectrum map in the specified subgroup actions. -/
def localSpectrumMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    C(LocalSpectrum H X.unop, LocalSpectrum H Y.unop) :=
  BanachSpectrum.comapContinuous (NormContinuousAction.homMap f.unop).toBoundedRingHom

omit [IsTopologicalGroup G] in
theorem localSpectrumMap_equivariant {X Y : NormContinuousSpace K H}
    (f : X ⟶ Y) (h : H) (x : LocalSpectrum H X.unop) :
    localSpectrumMap H f (h • x) = h • localSpectrumMap H f x :=
  NormContinuousAction.spectrumMap_equivariant f.unop h x

omit [IsTopologicalGroup G] in
private theorem localSpectrumMap_unit {X Y : NormContinuousSpace K H}
    (f : X ⟶ Y) (h : H) (x : LocalSpectrum H X.unop) :
    TopologicalInduction.unit H (localSpectrumMap H f (h • x)) =
      (h : G) • TopologicalInduction.unit H (localSpectrumMap H f x) := by
  rw [localSpectrumMap_equivariant, TopologicalInduction.unit_subgroup_smul]

/-- The actual quotient extension of the original equivariant spectrum map. -/
def balancedMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    C(Spectrum H X.unop, Spectrum H Y.unop) :=
  TopologicalInduction.extend
    ⟨fun x => TopologicalInduction.unit H (localSpectrumMap H f x),
      TopologicalInduction.continuous_unit.comp (localSpectrumMap H f).continuous⟩
    (localSpectrumMap_unit H f)

@[simp]
theorem balancedMap_mk {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (g : G) (x : LocalSpectrum H X.unop) :
    balancedMap H f (TopologicalInduction.mk H g x) =
      TopologicalInduction.mk H g (localSpectrumMap H f x) :=
  TopologicalInduction.smul_unit g _

theorem balancedMap_equivariant {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (g : G) (z : Spectrum H X.unop) :
    balancedMap H f (g • z) = g • balancedMap H f z :=
  TopologicalInduction.lift_smul _ (localSpectrumMap_unit H f) g z

/-- Induction of actual balanced spectra, with their original quotient topologies. -/
def balancedFunctor : NormContinuousSpace K H ⥤ ContAction TopCat.{max u v} G where
  obj := balancedAction H
  map f := ObjectProperty.homMk
    { hom := TopCat.ofHom (balancedMap H f)
      comm := fun g => by
        apply TopCat.ext
        intro z
        exact balancedMap_equivariant H f g z }
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      change balancedMap H (𝟙 X) (TopologicalInduction.mk H p.1 p.2) =
        TopologicalInduction.mk H p.1 p.2
      rw [balancedMap_mk]
      rfl
  map_comp f k := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply TopCat.ext
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      change balancedMap H (f ≫ k) (TopologicalInduction.mk H p.1 p.2) =
        balancedMap H k (balancedMap H f (TopologicalInduction.mk H p.1 p.2))
      rw [balancedMap_mk, balancedMap_mk, balancedMap_mk]
      rfl

/-- The actual family-to-quotient homeomorphism is natural in the bounded input map. -/
theorem spectrumHomeomorph_naturality (hH : IsOpen (H : Set G))
    {X Y : NormContinuousSpace K H} (f : X ⟶ Y) (p : (family H X.unop).Space) :
    spectrumHomeomorph H Y.unop hH ((familyMap H f).spectrumMap p) =
      balancedMap H f (spectrumHomeomorph H X.unop hH p) := by
  rcases p with ⟨c, x⟩
  exact (balancedMap_mk H f c.out x).symm

/-- Equivariant spectrum realization agrees naturally with actual quotient induction. -/
def spectrumComparison (hH : IsOpen (H : Set G)) :
    spectrumFunctor H hH ≅ balancedFunctor (K := K) H :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (Action.mkIso
      (TopCat.isoOfHomeo (spectrumHomeomorph H X.unop hH))
      (fun g => by
        apply TopCat.ext
        intro p
        exact (actionMap_realization H X.unop hH g p).symm)))
    (fun f => by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro p
      exact spectrumHomeomorph_naturality H hH f p)

theorem balancedMap_id (X : NormContinuousSpace K H) :
    balancedMap H (𝟙 X) = ContinuousMap.id (Spectrum H X.unop) :=
  congrArg (fun q : (balancedFunctor H).obj X ⟶ (balancedFunctor H).obj X =>
    q.hom.hom.hom) ((balancedFunctor H).map_id X)

theorem balancedMap_comp {X Y Z : NormContinuousSpace K H}
    (f : X ⟶ Y) (k : Y ⟶ Z) :
    balancedMap H (f ≫ k) = (balancedMap H k).comp (balancedMap H f) :=
  congrArg (fun q : (balancedFunctor H).obj X ⟶ (balancedFunctor H).obj Z =>
    q.hom.hom.hom) ((balancedFunctor H).map_comp f k)

section AtlasMaps

variable [CompleteSpace K] (hH : IsOpen (H : Set G))

/-- The already constructed actual quotient atlas, bundled as presentation data. -/
def atlasPresentation (X : NormContinuousSpace K H) :
    AffinoidAtlasPresentation.{u, max u v, v} K where
  space := TopCat.of (Spectrum H X.unop)
  atlas := atlas H X.unop hH

/-- Pulling a seminorm back along the retained algebra map supplies nonemptiness. -/
def mapChart {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : (atlas H X.unop hH).Index) : (atlas H Y.unop hH).Index :=
  (familyMap H f).chartTarget c

@[simp]
theorem mapChart_id (X : NormContinuousSpace K H)
    (c : (atlas H X.unop hH).Index) :
    mapChart H hH (𝟙 X) c = c := rfl

theorem mapChart_comp {X Y Z : NormContinuousSpace K H} (f : X ⟶ Y) (k : Y ⟶ Z)
    (c : (atlas H X.unop hH).Index) :
    mapChart H hH (f ≫ k) c = mapChart H hH k (mapChart H hH f c) := rfl

theorem mapChart_subset {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : (atlas H X.unop hH).Index) :
    balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart (mapChart H hH f c)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨localSpectrumMap H f x, (balancedMap_mk H f c.val.out x).symm⟩

/-- Every admissible target chart is forced to be the same-coset target. -/
theorem mapChart_eq {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : (atlas H X.unop hH).Index) (d : (atlas H Y.unop hH).Index)
    (h : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart d)) :
    mapChart H hH f c = d := by
  apply (familyMap H f).chartTarget_eq c d
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨y, (spectrumHomeomorph H Y.unop hH).injective ?_⟩
  exact hy.trans (spectrumHomeomorph_naturality H hH f ⟨c.val, x⟩).symm

/-- For every admissible pair, keep the original equivariant bounded pullback. -/
def mapPullback {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : (atlas H X.unop hH).Index) (d : (atlas H Y.unop hH).Index)
    (_h : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart d)) :
    BoundedAlgHom K ((atlas H Y.unop hH).algebra d) ((atlas H X.unop hH).algebra c) :=
  NormContinuousAction.homMap f.unop

theorem mapPullback_chart {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c : (atlas H X.unop hH).Index) (d : (atlas H Y.unop hH).Index)
    (h : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart d))
    (x : BanachSpectrum ((atlas H X.unop hH).algebra c)) :
    (atlas H Y.unop hH).chart d
        (BanachSpectrum.comap (mapPullback H hH f c d h).toBoundedRingHom x) =
      balancedMap H f ((atlas H X.unop hH).chart c x) := by
  have hd := mapChart_eq H hH f c d h
  subst d
  exact (balancedMap_mk H f c.val.out x).symm

/-- Both atlas restrictions commute with the retained bounded algebra maps. -/
theorem mapPullback_naturality {X Y : NormContinuousSpace K H} (f : X ⟶ Y)
    (c c' : (atlas H X.unop hH).Index) (d d' : (atlas H Y.unop hH).Index)
    (hc : Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H X.unop hH).chart c'))
    (hd : Set.range ((atlas H Y.unop hH).chart d) ⊆
      Set.range ((atlas H Y.unop hH).chart d'))
    (h : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart d))
    (h' : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c') ⊆
      Set.range ((atlas H Y.unop hH).chart d')) :
    ((atlas H X.unop hH).restriction c c' hc).comp (mapPullback H hH f c' d' h') =
      (mapPullback H hH f c d h).comp ((atlas H Y.unop hH).restriction d d' hd) := by
  have hcc' := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
    (spectrumHomeomorph H X.unop hH) c c' hc
  have hdd' := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H Y.unop).algebra
    (spectrumHomeomorph H Y.unop hH) d d' hd
  subst c'
  subst d'
  rw [(atlas H X.unop hH).restriction_id, (atlas H Y.unop hH).restriction_id]
  exact BoundedAlgHom.ext fun _ => rfl

/-- The quotient map together with all admissible bounded chart pullbacks. -/
def strongMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    AffinoidAtlasPresentation.StrongHom
      (atlasPresentation H hH X) (atlasPresentation H hH Y) where
  baseMap := balancedMap H f
  target_exists c := ⟨mapChart H hH f c, mapChart_subset H hH f c⟩
  pullback := mapPullback H hH f
  chart_comm := mapPullback_chart H hH f
  restriction_comm := mapPullback_naturality H hH f

/-- The same actual map, choosing the uniquely admissible target coset chart. -/
def atlasMap {X Y : NormContinuousSpace K H} (f : X ⟶ Y) :
    atlasPresentation H hH X ⟶ atlasPresentation H hH Y where
  baseMap := balancedMap H f
  indexMap := mapChart H hH f
  index_mono c c' hc := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c c' hc
    subst c'
    exact Set.Subset.rfl
  pullback _ := NormContinuousAction.homMap f.unop
  chart_comm c x := (balancedMap_mk H f c.val.out x).symm
  restriction_comm c c' hc := by
    have he := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X.unop).algebra
      (spectrumHomeomorph H X.unop hH) c c' hc
    subst c'
    exact mapPullback_naturality H hH f c c
      (mapChart H hH f c) (mapChart H hH f c) hc Set.Subset.rfl
      (mapChart_subset H hH f c) (mapChart_subset H hH f c)

@[simp]
theorem atlasMap_id (X : NormContinuousSpace K H) :
    atlasMap H hH (𝟙 X) = 𝟙 (atlasPresentation H hH X) :=
  AffinoidAtlasPresentation.Hom.ext (balancedMap_id H X) rfl (heq_of_eq rfl)

theorem atlasMap_comp {X Y Z : NormContinuousSpace K H} (f : X ⟶ Y) (k : Y ⟶ Z) :
    atlasMap H hH (f ≫ k) = atlasMap H hH f ≫ atlasMap H hH k :=
  AffinoidAtlasPresentation.Hom.ext (balancedMap_comp H f k) rfl (heq_of_eq rfl)

/-- Actual quotient induction is functorial in the category of bounded chosen atlas maps. -/
def atlasFunctor : NormContinuousSpace K H ⥤
    AffinoidAtlasPresentation.{u, max u v, v} K where
  obj := atlasPresentation H hH
  map := atlasMap H hH
  map_id := atlasMap_id H hH
  map_comp := atlasMap_comp H hH

/-- At the identity the all-admissible map is the bounded identity. -/
theorem mapPullback_id (X : NormContinuousSpace K H)
    (c : (atlas H X.unop hH).Index)
    (h : balancedMap H (𝟙 X) '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H X.unop hH).chart c)) :
    mapPullback H hH (𝟙 X) c c h = BoundedAlgHom.id K ((atlas H X.unop hH).algebra c) :=
  rfl

/-- All admissible pullbacks compose in the original, possibly nonreduced algebras. -/
theorem mapPullback_comp {X Y Z : NormContinuousSpace K H} (f : X ⟶ Y) (k : Y ⟶ Z)
    (c : (atlas H X.unop hH).Index) (d : (atlas H Y.unop hH).Index)
    (e : (atlas H Z.unop hH).Index)
    (hf : balancedMap H f '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Y.unop hH).chart d))
    (hk : balancedMap H k '' Set.range ((atlas H Y.unop hH).chart d) ⊆
      Set.range ((atlas H Z.unop hH).chart e))
    (hfk : balancedMap H (f ≫ k) '' Set.range ((atlas H X.unop hH).chart c) ⊆
      Set.range ((atlas H Z.unop hH).chart e)) :
    mapPullback H hH (f ≫ k) c e hfk =
      (mapPullback H hH f c d hf).comp (mapPullback H hH k d e hk) := rfl

end AtlasMaps

end Langlands.Analytic.PresentedAffinoidAlgebra.InducedAction
