import Langlands.Geometry.Analytic.DisjointAffinoidMorphisms
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalAtlas
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalChartTransport

/-! # Bounded transport on the actual induced affinoid atlases -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The actual positive-polyradius quotient family underlying the induced atlas. -/
def inducedAffinoidObject (X : ρ.OpenSubgroupTransport) : AffinoidFamily.{u, v} K :=
  ⟨G ⧸ X.subgroup.toSubgroup, X.inducedAffinoidFamily⟩

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

@[simp]
theorem cosetChartPullback_id (X : ρ.OpenSubgroupTransport)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (𝟙 X : X ⟶ X).cosetChartPullback c =
      BoundedAlgHom.id K X.domain.obj.algebra := by
  simpa only [cosetChartPullback, cosetMap_id] using chartPullback_id X c.out

theorem cosetChartPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (f ≫ g).cosetChartPullback c =
      (f.cosetChartPullback c).comp (g.cosetChartPullback (f.cosetMap c)) := by
  simpa only [cosetChartPullback, cosetMap_comp] using
    f.chartPullback_comp g c.out (f.cosetMap c).out
      (g.cosetMap (f.cosetMap c)).out (f.cosetChart_compatible c)
      (g.cosetChart_compatible (f.cosetMap c))
      (by simpa only [cosetMap_comp] using (f ≫ g).cosetChart_compatible c)

/-- Conjugate the actual rational quotient pullback by the bounded radius-one
quotient equivalences. The coset representative correction is retained. -/
def affinoidChartPullback (f : X ⟶ Y) (c : G ⧸ X.subgroup.toSubgroup) :
    BoundedAlgHom K Y.inducedChartAlgebra X.inducedChartAlgebra :=
  (PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm.toBoundedAlgHom.comp
    ((f.cosetChartPullback c).comp
      (PresentedAffinoidAlgebra.strictEquiv K Y.domain.obj.algebra).toBoundedAlgHom)

@[simp]
theorem affinoidChartPullback_id (X : ρ.OpenSubgroupTransport)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (𝟙 X : X ⟶ X).affinoidChartPullback c =
      BoundedAlgHom.id K X.inducedChartAlgebra := by
  unfold affinoidChartPullback
  rw [cosetChartPullback_id]
  exact BoundedAlgHom.ext fun a =>
    (PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm_apply_apply a

theorem affinoidChartPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (f ≫ g).affinoidChartPullback c =
      (f.affinoidChartPullback c).comp (g.affinoidChartPullback (f.cosetMap c)) := by
  unfold affinoidChartPullback
  rw [cosetChartPullback_comp]
  apply BoundedAlgHom.ext
  intro a
  change (PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (f.cosetChartPullback c (g.cosetChartPullback (f.cosetMap c)
        (PresentedAffinoidAlgebra.strictEquiv K Z.domain.obj.algebra a))) =
    (PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (f.cosetChartPullback c
        ((PresentedAffinoidAlgebra.strictEquiv K Y.domain.obj.algebra)
          ((PresentedAffinoidAlgebra.strictEquiv K Y.domain.obj.algebra).symm
            (g.cosetChartPullback (f.cosetMap c)
              (PresentedAffinoidAlgebra.strictEquiv K Z.domain.obj.algebra a)))))
  rw [BoundedAlgEquiv.apply_symm_apply]

/-- The actual componentwise bounded transport of the quotient families. -/
def affinoidFamilyMap (f : X ⟶ Y) : X.inducedAffinoidObject ⟶ Y.inducedAffinoidObject where
  indexMap := f.cosetMap
  pullback := f.affinoidChartPullback

@[simp]
theorem affinoidFamilyMap_id (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).affinoidFamilyMap = 𝟙 X.inducedAffinoidObject := by
  apply AffinoidFamily.Hom.ext (funext (cosetMap_id X))
  exact heq_of_eq (funext (affinoidChartPullback_id X))

theorem affinoidFamilyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).affinoidFamilyMap = f.affinoidFamilyMap ≫ g.affinoidFamilyMap := by
  apply AffinoidFamily.Hom.ext (funext (cosetMap_comp f g))
  exact heq_of_eq (funext (affinoidChartPullback_comp f g))

/-- The spectrum comap is the strict chart map in the constructed generalized
quotient coordinates. This follows from the actual algebra inverse laws. -/
theorem affinoidChartPullback_spectrum (f : X ⟶ Y)
    (c : G ⧸ X.subgroup.toSubgroup) (x : BanachSpectrum X.inducedChartAlgebra) :
    Y.localAffinoidSpectrumHomeomorph.symm
        (BanachSpectrum.comap (f.affinoidChartPullback c).toBoundedRingHom x) =
      f.cosetChartSpectrumMap c (X.localAffinoidSpectrumHomeomorph.symm x) := by
  apply BanachSpectrum.ext
  intro a
  change x ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (f.cosetChartPullback c
        ((PresentedAffinoidAlgebra.strictEquiv K Y.domain.obj.algebra)
          ((PresentedAffinoidAlgebra.strictEquiv K Y.domain.obj.algebra).symm a)))) =
    x ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (f.cosetChartPullback c a))
  rw [BoundedAlgEquiv.apply_symm_apply]

/-- The bounded family morphism realizes the already constructed induced
transport on the actual balanced quotient, through the actual homeomorphisms. -/
theorem affinoidFamilyMap_realization (f : X ⟶ Y) (p : X.inducedAffinoidObject.Space) :
    f.inducedMap (X.inducedAffinoidHomeomorph p) =
      Y.inducedAffinoidHomeomorph (f.affinoidFamilyMap.spectrumMap p) := by
  change DisjointAffinoidAtlas.Space X.inducedAffinoidFamily at p
  rcases p with ⟨c, x⟩
  change BanachSpectrum X.inducedChartAlgebra at x
  change f.inducedMap (X.inducedChart c.out (X.localAffinoidSpectrumHomeomorph.symm x)) =
    Y.inducedChart (f.cosetMap c).out
      (Y.localAffinoidSpectrumHomeomorph.symm
        (BanachSpectrum.comap (f.affinoidChartPullback c).toBoundedRingHom x))
  exact (f.inducedChart_chartSpectrumMap c.out (f.cosetMap c).out
    (f.cosetChart_compatible c) _).symm.trans
      (congrArg (Y.inducedChart (f.cosetMap c).out)
        (f.affinoidChartPullback_spectrum c x).symm)

/-- The target chart exists even when other component spectra are empty. -/
def atlasTarget (f : X ⟶ Y) (c : X.inducedAffinoidAtlas.Index) :
    Y.inducedAffinoidAtlas.Index :=
  f.affinoidFamilyMap.chartTarget c

theorem image_atlasChart_subset (f : X ⟶ Y) (c : X.inducedAffinoidAtlas.Index) :
    f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart (f.atlasTarget c)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (f.affinoidChartPullback c.val).toBoundedRingHom x,
    (f.affinoidFamilyMap_realization ⟨c.val, x⟩).symm⟩

/-- Pull the containment condition back through the actual chart homeomorphisms. -/
theorem disjointChart_containment (f : X ⟶ Y)
    (c : X.inducedAffinoidAtlas.Index) (d : Y.inducedAffinoidAtlas.Index)
    (h : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d)) :
    f.affinoidFamilyMap.spectrumMap ''
        DisjointAffinoidAtlas.chartDomain X.inducedAffinoidFamily c ⊆
      DisjointAffinoidAtlas.chartDomain Y.inducedAffinoidFamily d := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨y, Y.inducedAffinoidHomeomorph.injective ?_⟩
  exact hy.trans (f.affinoidFamilyMap_realization ⟨c.val, x⟩)

/-- Every admissible target chart is the chosen target component. -/
theorem atlasTarget_eq (f : X ⟶ Y)
    (c : X.inducedAffinoidAtlas.Index) (d : Y.inducedAffinoidAtlas.Index)
    (h : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d)) : f.atlasTarget c = d :=
  f.affinoidFamilyMap.chartTarget_eq c d (f.disjointChart_containment c d h)

/-- The actual bounded pullback for every admissible pair of atlas charts.
The algebras are constant within each family; containment identifies the
chosen target index, not the algebra homomorphism. -/
def atlasPullback (f : X ⟶ Y)
    (c : X.inducedAffinoidAtlas.Index) (d : Y.inducedAffinoidAtlas.Index)
    (_h : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d)) :
    BoundedAlgHom K (Y.inducedAffinoidAtlas.algebra d)
      (X.inducedAffinoidAtlas.algebra c) :=
  f.affinoidChartPullback c.val

theorem atlasPullback_chart (f : X ⟶ Y)
    (c : X.inducedAffinoidAtlas.Index) (d : Y.inducedAffinoidAtlas.Index)
    (h : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d))
    (x : BanachSpectrum (X.inducedAffinoidAtlas.algebra c)) :
    Y.inducedAffinoidAtlas.chart d
        (BanachSpectrum.comap (f.atlasPullback c d h).toBoundedRingHom x) =
      f.inducedMap (X.inducedAffinoidAtlas.chart c x) := by
  have hd := f.atlasTarget_eq c d h
  subst d
  exact (f.affinoidFamilyMap_realization ⟨c.val, x⟩).symm

/-- Algebra naturality with restrictions in both atlases. -/
theorem atlasPullback_naturality (f : X ⟶ Y)
    (c c' : X.inducedAffinoidAtlas.Index) (d d' : Y.inducedAffinoidAtlas.Index)
    (hcc' : Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart c'))
    (hdd' : Set.range (Y.inducedAffinoidAtlas.chart d) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d'))
    (h : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d))
    (h' : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c') ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d')) :
    (X.inducedAffinoidAtlas.restriction c c' hcc').comp (f.atlasPullback c' d' h') =
      (f.atlasPullback c d h).comp (Y.inducedAffinoidAtlas.restriction d d' hdd') := by
  rw [X.inducedAffinoidAtlas_restriction_eq, Y.inducedAffinoidAtlas_restriction_eq]
  have hc := X.inducedAffinoidAtlas_index_eq_of_subset c c' hcc'
  subst c'
  rfl

@[simp]
theorem atlasPullback_id (X : ρ.OpenSubgroupTransport) (c : X.inducedAffinoidAtlas.Index)
    (h : (𝟙 X : X ⟶ X).inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart c)) :
    (𝟙 X : X ⟶ X).atlasPullback c c h =
      BoundedAlgHom.id K (X.inducedAffinoidAtlas.algebra c) :=
  affinoidChartPullback_id X c.val

/-- Contravariant algebra composition for every compatible triple of atlas charts. -/
theorem atlasPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : X.inducedAffinoidAtlas.Index) (d : Y.inducedAffinoidAtlas.Index)
    (e : Z.inducedAffinoidAtlas.Index)
    (hfd : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d))
    (hge : g.inducedMap '' Set.range (Y.inducedAffinoidAtlas.chart d) ⊆
      Set.range (Z.inducedAffinoidAtlas.chart e))
    (hfe : (f ≫ g).inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Z.inducedAffinoidAtlas.chart e)) :
    (f ≫ g).atlasPullback c e hfe =
      (f.atlasPullback c d hfd).comp (g.atlasPullback d e hge) := by
  have hd : d.val = f.cosetMap c.val :=
    congrArg Subtype.val (f.atlasTarget_eq c d hfd).symm
  change (f ≫ g).affinoidChartPullback c.val =
    (f.affinoidChartPullback c.val).comp (g.affinoidChartPullback d.val)
  rw [hd, affinoidChartPullback_comp]

end Hom

/-- Actual quotient algebras and bounded transport form a functor.
Its spectrum realization is the existing induced-space transport. -/
def inducedAffinoidTransportFunctor :
    ρ.OpenSubgroupTransport ⥤ AffinoidFamily.{u, v} K where
  obj := inducedAffinoidObject
  map := Hom.affinoidFamilyMap
  map_id := Hom.affinoidFamilyMap_id
  map_comp := Hom.affinoidFamilyMap_comp

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
