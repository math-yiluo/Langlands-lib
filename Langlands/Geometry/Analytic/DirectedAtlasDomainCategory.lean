import Langlands.Geometry.Analytic.DirectedAtlasDomainRestrictions
import Mathlib.Topology.Category.TopCat.ULift

/-! # Actual domains represented in directed original atlas charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  (a : IndexedAffinoidAtlas.{u, v, w} K X) (hd : a.HasDirectedCharts)

/-- A full affinoid-domain representation in one original chart of a directed
atlas. Distinct choices of chart or presentation remain distinct objects. -/
structure DirectedDomain (hd : a.HasDirectedCharts) where
  index : a.Index
  domain : Domain K (a.algebra index)

namespace DirectedDomain

variable {a hd}

/-- The actual finite positive-polyradius quotient representing the domain. -/
abbrev algebra (U : DirectedDomain a hd) : PresentedAffinoidAlgebra K :=
  U.domain.algebra

/-- The represented subset of the original ambient space. -/
def locus (U : DirectedDomain a hd) : Set X :=
  a.chart U.index '' U.domain.locus

/-- The actual spectrum map to the ambient space. -/
def ambientMap (U : DirectedDomain a hd) : C(BanachSpectrum U.algebra, X) where
  toFun x := a.chart U.index (U.domain.spectrumMap x)
  continuous_toFun :=
    (a.isEmbedding_chart U.index).continuous.comp U.domain.spectrumMap.continuous

theorem range_ambientMap (U : DirectedDomain a hd) :
    Set.range U.ambientMap = U.locus := by
  change Set.range (a.chart U.index ∘ U.domain.spectrumMap) =
    a.chart U.index '' U.domain.locus
  rw [Set.range_comp]
  exact congrArg (fun s => a.chart U.index '' s) U.domain.represents.2.1

/-- No injectivity of the full-domain structural spectrum map is assumed. -/
def spectrumToLocus (U : DirectedDomain a hd) :
    C(BanachSpectrum U.algebra, U.locus) where
  toFun x := ⟨U.ambientMap x, U.range_ambientMap ▸ Set.mem_range_self x⟩
  continuous_toFun := U.ambientMap.continuous.subtype_mk _

theorem spectrumToLocus_surjective (U : DirectedDomain a hd) :
    Function.Surjective U.spectrumToLocus := by
  intro x
  have hx : x.val ∈ Set.range U.ambientMap := by
    rw [U.range_ambientMap]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

theorem isCompact_locus (U : DirectedDomain a hd) : IsCompact U.locus := by
  rw [← U.range_ambientMap]
  exact isCompact_range U.ambientMap.continuous

/-- Actual bounded restrictions, with their structural equations over every
common original upper chart and their ambient containment. -/
structure Inclusion (U V : DirectedDomain a hd) where
  subset : U.locus ⊆ V.locus
  restriction : BoundedAlgHom K V.algebra U.algebra
  comp_baseMap : ∀ (q : a.Index)
    (hUq : Set.range (a.chart U.index) ⊆ Set.range (a.chart q))
    (hVq : Set.range (a.chart V.index) ⊆ Set.range (a.chart q)),
    restriction.comp (V.domain.baseMap.comp (a.restriction V.index q hVq)) =
      U.domain.baseMap.comp (a.restriction U.index q hUq)

namespace Inclusion

variable {U V W : DirectedDomain a hd}

@[ext]
theorem ext {f g : Inclusion U V} (h : f.restriction = g.restriction) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Full representation uniqueness, rather than spectrum-point separation,
identifies every competing entire bounded map. -/
theorem restriction_eq (f : Inclusion U V) :
    f.restriction =
      a.directedDomainRestriction hd U.index V.index U.domain V.domain f.subset := by
  obtain ⟨q, hUq, hVq⟩ := hd U.index V.index
  exact a.eq_directedDomainRestriction_of_over_base hd U.index V.index
    U.domain V.domain f.subset q hUq hVq f.restriction (f.comp_baseMap q hUq hVq)

instance : Subsingleton (Inclusion U V) := ⟨fun f g => by
  apply ext
  exact f.restriction_eq.trans g.restriction_eq.symm⟩

/-- Every ambient containment constructs a bounded restriction by the published
directed full-factorization construction. -/
def ofSubset (U V : DirectedDomain a hd) (h : U.locus ⊆ V.locus) : Inclusion U V where
  subset := h
  restriction := a.directedDomainRestriction hd U.index V.index U.domain V.domain h
  comp_baseMap := a.directedDomainRestriction_comp_baseMap hd U.index V.index
    U.domain V.domain h

def id (U : DirectedDomain a hd) : Inclusion U U where
  subset := Subset.rfl
  restriction := BoundedAlgHom.id K U.algebra
  comp_baseMap _ _ _ := rfl

/-- Composition retains the actual composite bounded map. Its equation over
each upper chart follows from the constructed restriction's coherence. -/
def comp (f : Inclusion U V) (g : Inclusion V W) : Inclusion U W where
  subset := f.subset.trans g.subset
  restriction := f.restriction.comp g.restriction
  comp_baseMap q hUq hWq := by
    rw [f.restriction_eq, g.restriction_eq,
      a.directedDomainRestriction_comp hd U.index V.index W.index
        U.domain V.domain W.domain f.subset g.subset (f.subset.trans g.subset)]
    exact a.directedDomainRestriction_comp_baseMap hd U.index W.index
      U.domain W.domain (f.subset.trans g.subset) q hUq hWq

end Inclusion

/-- The category consists of actual represented domains and bounded algebra
restrictions. Thinness is proved by the full universal properties. -/
instance : Category (DirectedDomain a hd) where
  Hom := Inclusion
  id := Inclusion.id
  comp := Inclusion.comp
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

theorem nonempty_hom_iff_subset (U V : DirectedDomain a hd) :
    Nonempty (U ⟶ V) ↔ U.locus ⊆ V.locus :=
  ⟨fun ⟨f⟩ => f.subset, fun h => ⟨Inclusion.ofSubset U V h⟩⟩

namespace Inclusion

variable {U V W : DirectedDomain a hd}

@[simp]
theorem restriction_id (U : DirectedDomain a hd) :
    (𝟙 U : U ⟶ U).restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp]
theorem restriction_comp (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).restriction = f.restriction.comp g.restriction := rfl

def spectrumMap (f : U ⟶ V) :
    C(BanachSpectrum U.algebra, BanachSpectrum V.algebra) :=
  BanachSpectrum.comapContinuous f.restriction.toBoundedRingHom

theorem ambientMap_naturality (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.ambientMap (f.spectrumMap x) = U.ambientMap x := by
  change a.chart V.index (V.domain.spectrumMap
    (BanachSpectrum.comap f.restriction.toBoundedRingHom x)) =
      a.chart U.index (U.domain.spectrumMap x)
  rw [f.restriction_eq]
  exact a.directedDomainRestriction_chart hd U.index V.index
    U.domain V.domain f.subset x

def locusMap (f : U ⟶ V) : C(U.locus, V.locus) where
  toFun x := ⟨x.val, f.subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem spectrumToLocus_naturality (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.spectrumToLocus (f.spectrumMap x) = f.locusMap (U.spectrumToLocus x) :=
  Subtype.ext (f.ambientMap_naturality x)

end Inclusion

variable (a hd)

/-- Realize all domains by their actual affinoid algebras and bounded maps. -/
def toAffinoidSpace : DirectedDomain a hd ⥤ PresentedAffinoidSpace K where
  obj U := Opposite.op U.algebra
  map f := Quiver.Hom.op f.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

def toTopologicalSpace : DirectedDomain a hd ⥤ TopCat.{u} :=
  toAffinoidSpace a hd ⋙ affinoidSpectrumFunctor K

/-- The actual ambient subspaces with continuous inclusions. -/
def locusFunctor : DirectedDomain a hd ⥤ TopCat.{v} where
  obj U := TopCat.of U.locus
  map f := TopCat.ofHom f.locusMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The two independent realization universes are lifted to a common universe.
The components are continuous surjections, not asserted homeomorphisms. -/
def spectrumToLocusNat :
    toTopologicalSpace a hd ⋙ TopCat.uliftFunctor.{v} ⟶
      locusFunctor a hd ⋙ TopCat.uliftFunctor.{u} where
  app U := TopCat.ofHom
    ⟨fun x => ULift.up (U.spectrumToLocus x.down),
      continuous_uliftUp.comp (U.spectrumToLocus.continuous.comp continuous_uliftDown)⟩
  naturality U V f := by
    apply TopCat.ext
    intro x
    apply ULift.ext
    exact f.spectrumToLocus_naturality x.down

/-- The presheaf retains all actual quotient algebras and bounded maps. -/
def boundedPresheaf : (DirectedDomain a hd)ᵒᵖ ⥤ PresentedAffinoidAlgebra K where
  obj U := U.unop.algebra
  map f := f.unop.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

def banachPresheaf : (DirectedDomain a hd)ᵒᵖ ⥤ BanachRing :=
  boundedPresheaf a hd ⋙ PresentedAffinoidAlgebra.toBanachRing K

/-- A fixed-chart domain arrow is retained with exactly its original bounded
restriction and the equations over all containing original charts. -/
def sameChartFunctor (i : a.Index) : Domain K (a.algebra i) ⥤ DirectedDomain a hd where
  obj U := ⟨i, U⟩
  map {U V} f :=
    { subset := Set.image_mono f.subset
      restriction := f.restriction
      comp_baseMap q hiq _ := by
        rw [← BoundedAlgHom.comp_assoc, f.comp_baseMap] }
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

/-- No information about same-chart bounded arrows is lost. The equation over
that chart itself recovers the original fixed-base equation. -/
def fullyFaithfulSameChartFunctor (i : a.Index) :
    (sameChartFunctor a hd i).FullyFaithful where
  preimage {U V} f := by
    change Inclusion (⟨i, U⟩ : DirectedDomain a hd) ⟨i, V⟩ at f
    refine { restriction := f.restriction, comp_baseMap := ?_ }
    have h := f.comp_baseMap i Subset.rfl Subset.rfl
    change f.restriction.comp (V.baseMap.comp (a.restriction i i Subset.rfl)) =
      U.baseMap.comp (a.restriction i i Subset.rfl) at h
    simpa only [a.restriction_id, BoundedAlgHom.comp_id] using h
  map_preimage _ := Inclusion.ext rfl
  preimage_map _ := Domain.Inclusion.ext rfl

instance (i : a.Index) : (sameChartFunctor a hd i).Full :=
  (fullyFaithfulSameChartFunctor a hd i).full

instance (i : a.Index) : (sameChartFunctor a hd i).Faithful :=
  (fullyFaithfulSameChartFunctor a hd i).faithful

@[simp]
theorem sameChartFunctor_map_restriction (i : a.Index)
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    ((sameChartFunctor a hd i).map f).restriction = f.restriction := rfl

theorem sameChartFunctor_comp_toAffinoidSpace (i : a.Index) :
    sameChartFunctor a hd i ⋙ toAffinoidSpace a hd =
      Domain.toAffinoidSpace K (a.algebra i) := rfl

theorem sameChartFunctor_comp_toTopologicalSpace (i : a.Index) :
    sameChartFunctor a hd i ⋙ toTopologicalSpace a hd =
      Domain.toTopologicalSpace K (a.algebra i) := rfl

variable {a hd}

/-- Equal ambient subsets construct an isomorphism even when the representing
algebras and their original charts differ. -/
def isoOfLocusEq (U V : DirectedDomain a hd) (h : U.locus = V.locus) : U ≅ V where
  hom := Inclusion.ofSubset U V (fun _ hx => h ▸ hx)
  inv := Inclusion.ofSubset V U (fun _ hx => h.symm ▸ hx)
  hom_inv_id := (inferInstance : Subsingleton (Inclusion U U)).elim _ _
  inv_hom_id := (inferInstance : Subsingleton (Inclusion V V)).elim _ _

theorem locus_eq_of_iso {U V : DirectedDomain a hd} (e : U ≅ V) :
    U.locus = V.locus :=
  Set.Subset.antisymm e.hom.subset e.inv.subset

theorem nonempty_iso_iff_locus_eq (U V : DirectedDomain a hd) :
    Nonempty (U ≅ V) ↔ U.locus = V.locus :=
  ⟨fun ⟨e⟩ => locus_eq_of_iso e, fun h => ⟨isoOfLocusEq U V h⟩⟩

/-- The actual inverse restrictions yield mutually inverse bounded algebra
maps; both full inverse identities come from the domain category. -/
def boundedEquivOfIso {U V : DirectedDomain a hd} (e : U ≅ V) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  BoundedAlgEquiv.ofHomInv e.inv.restriction e.hom.restriction
    (fun b => congrArg (fun f : U ⟶ U => f.restriction b) e.hom_inv_id)
    (fun b => congrArg (fun f : V ⟶ V => f.restriction b) e.inv_hom_id)

@[simp]
theorem boundedEquivOfIso_apply {U V : DirectedDomain a hd} (e : U ≅ V)
    (b : U.algebra) :
    boundedEquivOfIso e b = e.inv.restriction b := rfl

@[simp]
theorem boundedEquivOfIso_symm_apply {U V : DirectedDomain a hd} (e : U ≅ V)
    (b : V.algebra) :
    (boundedEquivOfIso e).symm b = e.hom.restriction b := rfl

/-- Changing the chart or the full domain representation of the same ambient
locus constructs an actual bounded equivalence of quotient algebras. -/
def boundedEquivOfLocusEq (U V : DirectedDomain a hd) (h : U.locus = V.locus) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  boundedEquivOfIso (isoOfLocusEq U V h)

def spectrumHomeomorphOfLocusEq (U V : DirectedDomain a hd) (h : U.locus = V.locus) :
    BanachSpectrum U.algebra ≃ₜ BanachSpectrum V.algebra :=
  (boundedEquivOfLocusEq U V h).spectrumHomeomorph.symm

theorem spectrumHomeomorphOfLocusEq_over_ambient (U V : DirectedDomain a hd)
    (h : U.locus = V.locus) (x : BanachSpectrum U.algebra) :
    V.ambientMap (spectrumHomeomorphOfLocusEq U V h x) = U.ambientMap x :=
  (isoOfLocusEq U V h).hom.ambientMap_naturality x

end DirectedDomain
end Langlands.Analytic.IndexedAffinoidAtlas
