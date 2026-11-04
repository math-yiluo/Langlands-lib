import Langlands.Geometry.Analytic.AtlasDomainRestrictions

/-! # The actual category of local full domains in arbitrary affinoid atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- An actual full affinoid-domain presentation in an original atlas chart.
The atlas is arbitrary; no directedness witness is part of the data. -/
structure LocalDomain where
  index : a.Index
  domain : Domain K (a.algebra index)

namespace LocalDomain

variable {a}

abbrev algebra (U : LocalDomain a) : PresentedAffinoidAlgebra K := U.domain.algebra

def locus (U : LocalDomain a) : Set X := a.chart U.index '' U.domain.locus

def ambientMap (U : LocalDomain a) : C(BanachSpectrum U.algebra, X) where
  toFun x := a.chart U.index (U.domain.spectrumMap x)
  continuous_toFun :=
    (a.isEmbedding_chart U.index).continuous.comp U.domain.spectrumMap.continuous

theorem range_ambientMap (U : LocalDomain a) : Set.range U.ambientMap = U.locus := by
  change Set.range (a.chart U.index ∘ U.domain.spectrumMap) =
    a.chart U.index '' U.domain.locus
  rw [Set.range_comp]
  exact congrArg (fun S => a.chart U.index '' S) U.domain.represents.2.1

theorem isEmbedding_ambientMap (U : LocalDomain a) : IsEmbedding U.ambientMap :=
  (a.isEmbedding_chart U.index).comp (Domain.spectrumEmbedding K _ U.domain).isEmbedding

/-- The actual spectrum is homeomorphic to its ambient subspace locus. -/
def locusHomeomorph (U : LocalDomain a) : BanachSpectrum U.algebra ≃ₜ U.locus :=
  U.isEmbedding_ambientMap.toHomeomorph.trans (Homeomorph.setCongr U.range_ambientMap)

@[simp]
theorem locusHomeomorph_apply_coe (U : LocalDomain a) (x : BanachSpectrum U.algebra) :
    (U.locusHomeomorph x : X) = U.ambientMap x := rfl

theorem isCompact_locus (U : LocalDomain a) : IsCompact U.locus := by
  rw [← U.range_ambientMap]
  exact isCompact_range U.ambientMap.continuous

/-- Morphisms retain actual bounded restrictions and their structural equations
over every original chart containing both local-domain images. -/
structure Inclusion (U V : LocalDomain a) where
  subset : U.locus ⊆ V.locus
  restriction : BoundedAlgHom K V.algebra U.algebra
  comp_chart : ∀ (q : a.Index)
    (hU : U.locus ⊆ Set.range (a.chart q)) (hV : V.locus ⊆ Set.range (a.chart q)),
    restriction.comp (a.domainChartRestriction V.index q V.domain hV) =
      a.domainChartRestriction U.index q U.domain hU

namespace Inclusion

variable {U V W : LocalDomain a}

@[ext]
theorem ext {f g : Inclusion U V} (h : f.restriction = g.restriction) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Every admitted actual restriction is the map constructed from containment. -/
theorem restriction_eq (f : Inclusion U V) :
    f.restriction = a.domainRestriction U.index V.index U.domain V.domain f.subset := by
  apply a.eq_domainRestriction_of_over_base U.index V.index U.domain V.domain f.subset
  have h := f.comp_chart V.index
    (a.domainSubset_chart U.index V.index U.domain V.domain f.subset)
    (a.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl)
  rw [a.domainChartRestriction_self] at h
  exact h

instance : Subsingleton (Inclusion U V) := ⟨fun f g => by
  apply ext
  exact f.restriction_eq.trans g.restriction_eq.symm⟩

/-- Ambient containment constructs the entire actual bounded restriction. -/
def ofSubset (U V : LocalDomain a) (h : U.locus ⊆ V.locus) : Inclusion U V where
  subset := h
  restriction := a.domainRestriction U.index V.index U.domain V.domain h
  comp_chart q hU hV :=
    a.domainRestriction_comp_chart U.index V.index q U.domain V.domain h hV hU

def id (U : LocalDomain a) : Inclusion U U where
  subset := Subset.rfl
  restriction := BoundedAlgHom.id K U.algebra
  comp_chart _ _ _ := rfl

/-- Composition stores the original contravariant composite algebra map. -/
def comp (f : Inclusion U V) (g : Inclusion V W) : Inclusion U W where
  subset := f.subset.trans g.subset
  restriction := f.restriction.comp g.restriction
  comp_chart q hU hW := by
    have hV := g.subset.trans hW
    rw [BoundedAlgHom.comp_assoc, g.comp_chart q hV hW, f.comp_chart q hU hV]

end Inclusion

/-- Full-test uniqueness proves thinness; morphisms themselves contain actual
bounded algebra maps and every original-chart structural equation. -/
instance : Category (LocalDomain a) where
  Hom := Inclusion
  id := Inclusion.id
  comp := Inclusion.comp
  id_comp _ := Inclusion.ext rfl
  comp_id _ := Inclusion.ext rfl
  assoc _ _ _ := Inclusion.ext rfl

theorem nonempty_hom_iff_subset (U V : LocalDomain a) :
    Nonempty (U ⟶ V) ↔ U.locus ⊆ V.locus :=
  ⟨fun ⟨f⟩ => f.subset, fun h => ⟨Inclusion.ofSubset U V h⟩⟩

namespace Inclusion

variable {U V W : LocalDomain a}

@[simp]
theorem restriction_id (U : LocalDomain a) :
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
  exact a.domainRestriction_chart U.index V.index U.domain V.domain f.subset x

def locusMap (f : U ⟶ V) : C(U.locus, V.locus) where
  toFun x := ⟨x.val, f.subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem locusHomeomorph_naturality (f : U ⟶ V) (x : BanachSpectrum U.algebra) :
    V.locusHomeomorph (f.spectrumMap x) = f.locusMap (U.locusHomeomorph x) :=
  Subtype.ext (f.ambientMap_naturality x)

/-- Every arrow is itself a full representation of its literal relative
ambient image in the target's spectrum. -/
theorem represents (f : U ⟶ V) :
    Represents K f.restriction (V.ambientMap ⁻¹' U.locus) := by
  rw [f.restriction_eq]
  exact a.domainRestriction_represents U.index V.index U.domain V.domain f.subset

end Inclusion

variable (a)

def toAffinoidSpace : LocalDomain a ⥤ PresentedAffinoidSpace K where
  obj U := Opposite.op U.algebra
  map f := Quiver.Hom.op f.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

def toTopologicalSpace : LocalDomain a ⥤ TopCat.{u} :=
  toAffinoidSpace a ⋙ affinoidSpectrumFunctor K

def locusFunctor : LocalDomain a ⥤ TopCat.{v} where
  obj U := TopCat.of U.locus
  map f := TopCat.ofHom f.locusMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The bounded presheaf retains the actual original quotient algebras and maps. -/
def boundedPresheaf : (LocalDomain a)ᵒᵖ ⥤ PresentedAffinoidAlgebra K where
  obj U := U.unop.algebra
  map f := f.unop.restriction
  map_id _ := rfl
  map_comp _ _ := rfl

def banachPresheaf : (LocalDomain a)ᵒᵖ ⥤ BanachRing :=
  boundedPresheaf a ⋙ PresentedAffinoidAlgebra.toBanachRing K

def sameChartFunctor (i : a.Index) : Domain K (a.algebra i) ⥤ LocalDomain a where
  obj U := ⟨i, U⟩
  map f :=
    { subset := Set.image_mono f.subset
      restriction := f.restriction
      comp_chart q hU hV := a.domainChartRestriction_naturality i q f hV hU }
  map_id _ := Inclusion.ext rfl
  map_comp _ _ := Inclusion.ext rfl

/-- Every fixed-chart actual restriction is retained and recovered. -/
def fullyFaithfulSameChartFunctor (i : a.Index) :
    (sameChartFunctor a i).FullyFaithful where
  preimage {U V} f := by
    change Inclusion (⟨i, U⟩ : LocalDomain a) ⟨i, V⟩ at f
    refine ⟨f.restriction, ?_⟩
    have h := f.comp_chart i
      (a.domainSubset_chart i i U U Subset.rfl)
      (a.domainSubset_chart i i V V Subset.rfl)
    simpa only [a.domainChartRestriction_self] using h
  map_preimage _ := Inclusion.ext rfl
  preimage_map _ := Domain.Inclusion.ext rfl

instance (i : a.Index) : (sameChartFunctor a i).Full :=
  (fullyFaithfulSameChartFunctor a i).full

instance (i : a.Index) : (sameChartFunctor a i).Faithful :=
  (fullyFaithfulSameChartFunctor a i).faithful

@[simp]
theorem sameChartFunctor_map_restriction (i : a.Index)
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    ((sameChartFunctor a i).map f).restriction = f.restriction := rfl

theorem sameChartFunctor_comp_toAffinoidSpace (i : a.Index) :
    sameChartFunctor a i ⋙ toAffinoidSpace a =
      Domain.toAffinoidSpace K (a.algebra i) := rfl

variable {a}

/-- Equal ambient subsets construct an isomorphism across arbitrary original charts. -/
def isoOfLocusEq (U V : LocalDomain a) (h : U.locus = V.locus) : U ≅ V where
  hom := Inclusion.ofSubset U V (fun _ hx => h ▸ hx)
  inv := Inclusion.ofSubset V U (fun _ hx => h.symm ▸ hx)
  hom_inv_id := @Subsingleton.elim (Inclusion U U) inferInstance _ _
  inv_hom_id := @Subsingleton.elim (Inclusion V V) inferInstance _ _

theorem locus_eq_of_iso {U V : LocalDomain a} (e : U ≅ V) :
    U.locus = V.locus :=
  Set.Subset.antisymm e.hom.subset e.inv.subset

theorem nonempty_iso_iff_locus_eq (U V : LocalDomain a) :
    Nonempty (U ≅ V) ↔ U.locus = V.locus :=
  ⟨fun ⟨e⟩ => locus_eq_of_iso e, fun h => ⟨isoOfLocusEq U V h⟩⟩

def boundedEquivOfIso {U V : LocalDomain a} (e : U ≅ V) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  BoundedAlgEquiv.ofHomInv e.inv.restriction e.hom.restriction
    (fun b => congrArg (fun f : U ⟶ U => f.restriction b) e.hom_inv_id)
    (fun b => congrArg (fun f : V ⟶ V => f.restriction b) e.inv_hom_id)

/-- Equal loci have actual mutually inverse bounded maps of their original
quotient algebras, even across unrelated original charts. -/
def boundedEquivOfLocusEq (U V : LocalDomain a) (h : U.locus = V.locus) :
    BoundedAlgEquiv K U.algebra V.algebra :=
  boundedEquivOfIso (isoOfLocusEq U V h)

def spectrumHomeomorphOfLocusEq (U V : LocalDomain a) (h : U.locus = V.locus) :
    BanachSpectrum U.algebra ≃ₜ BanachSpectrum V.algebra :=
  (boundedEquivOfLocusEq U V h).spectrumHomeomorph.symm

theorem spectrumHomeomorphOfLocusEq_over_ambient (U V : LocalDomain a)
    (h : U.locus = V.locus) (x : BanachSpectrum U.algebra) :
    V.ambientMap (spectrumHomeomorphOfLocusEq U V h x) = U.ambientMap x :=
  (isoOfLocusEq U V h).hom.ambientMap_naturality x

end LocalDomain
end Langlands.Analytic.IndexedAffinoidAtlas
