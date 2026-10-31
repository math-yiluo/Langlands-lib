import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomainLocalization

/-! # Full-domain localization through nested actual rational charts -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {d e h j : RationalChart K A}

/-- The actual ambient inclusion of an inner domain through a nested chart. -/
def nestedDomainInclusion (f : d ⟶ e) (U : Domain K d.algebra) :
    d.extendDomain U ⟶ e.toDomain :=
  d.extendDomainInclusion U ≫ (toDomainFunctor K A).map f

@[simp] theorem nestedDomainInclusion_restriction (f : d ⟶ e)
    (U : Domain K d.algebra) :
    (nestedDomainInclusion f U).restriction = U.baseMap.comp f.restriction := rfl

/-- Transport a full domain through an actual inclusion of rational charts.
The full representation is proved by ambient extension and localization. -/
def nestedDomain (f : d ⟶ e) (U : Domain K d.algebra) : Domain K e.algebra :=
  e.restrictDomain (d.extendDomain U) (nestedDomainInclusion f U)

@[simp] theorem nestedDomain_algebra (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedDomain f U).algebra = U.algebra := rfl

@[simp] theorem nestedDomain_baseMap (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedDomain f U).baseMap = U.baseMap.comp f.restriction := rfl

/-- The structural spectrum map is the actual composite of bounded maps. -/
theorem nestedDomain_spectrumMap (f : d ⟶ e) (U : Domain K d.algebra)
    (x : BanachSpectrum U.algebra) :
    (nestedDomain f U).spectrumMap x = f.spectrumMap (U.spectrumMap x) := by
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The inverse-image construction has exactly the image locus under the
actual bounded restriction's spectrum map. -/
theorem nestedDomain_locus (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedDomain f U).locus = f.spectrumMap '' U.locus := by
  change e.spectrumMap ⁻¹' (d.spectrumMap '' U.locus) = f.spectrumMap '' U.locus
  ext x
  constructor
  · rintro ⟨y, hy, heq⟩
    exact ⟨y, hy, e.spectrumMap_injective ((f.spectrumMap_over_base y).trans heq)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (f.spectrumMap_over_base y).symm⟩

/-- The actual restriction spectrum embedding identifies the two loci. -/
def nestedDomainLocusHomeomorph (f : d ⟶ e) (U : Domain K d.algebra) :
    U.locus ≃ₜ (nestedDomain f U).locus :=
  (f.isClosedEmbedding_spectrumMap.isEmbedding.homeomorphImage U.locus).trans
    (Homeomorph.setCongr (nestedDomain_locus f U).symm)

@[simp] theorem nestedDomainLocusHomeomorph_apply_coe (f : d ⟶ e)
    (U : Domain K d.algebra) (x : U.locus) :
    (nestedDomainLocusHomeomorph f U x : BanachSpectrum e.algebra) =
      f.spectrumMap x := rfl

/-- The locus comparison commutes with the actual structural spectrum maps. -/
theorem nestedDomain_spectrumToLocus (f : d ⟶ e) (U : Domain K d.algebra)
    (x : BanachSpectrum U.algebra) :
    (nestedDomain f U).spectrumToLocus x =
      nestedDomainLocusHomeomorph f U (U.spectrumToLocus x) :=
  Subtype.ext (nestedDomain_spectrumMap f U x)

/-- Inner bounded restrictions remain unchanged through the nested chart. -/
def nestedDomainFunctor (f : d ⟶ e) : Domain K d.algebra ⥤ Domain K e.algebra where
  obj := nestedDomain f
  map {U V} k := ⟨k.restriction, by
    change k.restriction.comp (V.baseMap.comp f.restriction) =
      U.baseMap.comp f.restriction
    rw [← BoundedAlgHom.comp_assoc, k.comp_baseMap]⟩
  map_id _ := Domain.Inclusion.ext rfl
  map_comp _ _ := Domain.Inclusion.ext rfl

@[simp] theorem nestedDomainFunctor_map_restriction (f : d ⟶ e)
    {U V : Domain K d.algebra} (k : U ⟶ V) :
    ((nestedDomainFunctor f).map k).restriction = k.restriction := rfl

/-- Actual inner inclusions give the naturality square on represented loci. -/
theorem nestedDomainLocusHomeomorph_naturality (f : d ⟶ e)
    {U V : Domain K d.algebra} (k : U ⟶ V) (x : U.locus) :
    nestedDomainLocusHomeomorph f V (k.locusMap x) =
      ((nestedDomainFunctor f).map k).locusMap
        (nestedDomainLocusHomeomorph f U x) :=
  Subtype.ext rfl

/-- The locus comparisons are natural isomorphisms of actual topological
space diagrams, with the original bounded-map spectrum realization. -/
def nestedDomainLocusNatIso (f : d ⟶ e) :
    Domain.locusFunctor K d.algebra ≅
      nestedDomainFunctor f ⋙ Domain.locusFunctor K e.algebra :=
  NatIso.ofComponents (fun U => TopCat.isoOfHomeo (nestedDomainLocusHomeomorph f U))
    (by
      intro U V k
      apply TopCat.ext
      intro x
      exact nestedDomainLocusHomeomorph_naturality f k x)

theorem nestedDomainLocusNatIso_spectrumToLocus (f : d ⟶ e) :
    Domain.spectrumToLocusNat K d.algebra ≫ (nestedDomainLocusNatIso f).hom =
      Functor.whiskerLeft (nestedDomainFunctor f)
        (Domain.spectrumToLocusNat K e.algebra) := by
  apply NatTrans.ext
  funext U
  apply TopCat.ext
  intro x
  exact (nestedDomain_spectrumToLocus f U x).symm

/-- Extending to the original base recovers the original inner extension,
with identity bounded maps on the retained algebra. -/
def extendNestedDomainIso (f : d ⟶ e) (U : Domain K d.algebra) :
    e.extendDomain (nestedDomain f U) ≅ d.extendDomain U :=
  e.extendRestrictDomainIso (d.extendDomain U) (nestedDomainInclusion f U)

@[simp] theorem extendNestedDomainIso_hom_restriction (f : d ⟶ e)
    (U : Domain K d.algebra) :
    (extendNestedDomainIso f U).hom.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem extendNestedDomainIso_inv_restriction (f : d ⟶ e)
    (U : Domain K d.algebra) :
    (extendNestedDomainIso f U).inv.restriction = BoundedAlgHom.id K U.algebra := rfl

/-- This comparison is natural for every actual inner domain inclusion. -/
def extendNestedDomainNatIso (f : d ⟶ e) :
    nestedDomainFunctor f ⋙ e.extendDomainFunctor ≅ d.extendDomainFunctor :=
  NatIso.ofComponents (extendNestedDomainIso f)
    (by intro U V k; apply Domain.Inclusion.ext; rfl)

/-- The localization equivalences commute with the actual over-category
postcomposition functor attached to the nested chart inclusion. -/
def nestedLocalizationNatIso (f : d ⟶ e) :
    nestedDomainFunctor f ⋙ e.extendDomainOverFunctor ≅
      d.extendDomainOverFunctor ⋙ Over.map ((toDomainFunctor K A).map f) :=
  NatIso.ofComponents (fun U => Over.isoMk (extendNestedDomainIso f U)
    (by apply Domain.Inclusion.ext; rfl))
    (by intro U V k; apply Over.OverMorphism.ext; apply Domain.Inclusion.ext; rfl)

/-- The inverse localization square also keeps identity bounded maps on
each ambient domain algebra. -/
def nestedRestrictDomainIso (f : d ⟶ e) (V : Over d.toDomain) :
    nestedDomain f (d.restrictDomain V.left V.hom) ≅
      e.restrictDomain V.left (V.hom ≫ (toDomainFunctor K A).map f) where
  hom := ⟨BoundedAlgHom.id K V.left.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K V.left.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

@[simp] theorem nestedRestrictDomainIso_hom_restriction (f : d ⟶ e)
    (V : Over d.toDomain) :
    (nestedRestrictDomainIso f V).hom.restriction =
      BoundedAlgHom.id K V.left.algebra := rfl

@[simp] theorem nestedRestrictDomainIso_inv_restriction (f : d ⟶ e)
    (V : Over d.toDomain) :
    (nestedRestrictDomainIso f V).inv.restriction =
      BoundedAlgHom.id K V.left.algebra := rfl

def nestedRestrictionNatIso (f : d ⟶ e) :
    d.restrictDomainFunctor ⋙ nestedDomainFunctor f ≅
      Over.map ((toDomainFunctor K A).map f) ⋙ e.restrictDomainFunctor :=
  NatIso.ofComponents (nestedRestrictDomainIso f)
    (by intro U V k; apply Domain.Inclusion.ext; rfl)

/-- Nested transport is fully faithful by rational quotient uniqueness over
A, applied to the base equation of the transported bounded restriction. -/
def fullyFaithfulNestedDomain (f : d ⟶ e) : (nestedDomainFunctor f).FullyFaithful where
  preimage {U V} k := ⟨k.restriction, by
    apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
      U.algebra d.generates
    apply BoundedAlgHom.ext
    intro a
    have hf := congrArg (fun q : BoundedAlgHom K A d.algebra => q a) f.comp_baseMap
    have hk := congrArg (fun q : BoundedAlgHom K e.algebra U.algebra =>
      q (e.baseMap a)) k.comp_baseMap
    change f.restriction (e.baseMap a) = d.baseMap a at hf
    change k.restriction (V.baseMap (d.baseMap a)) = U.baseMap (d.baseMap a)
    change k.restriction (V.baseMap (f.restriction (e.baseMap a))) =
      U.baseMap (f.restriction (e.baseMap a)) at hk
    exact (congrArg (fun b : d.algebra => k.restriction (V.baseMap b)) hf).symm.trans
      (hk.trans (congrArg U.baseMap hf))⟩
  map_preimage _ := Domain.Inclusion.ext rfl
  preimage_map _ := Domain.Inclusion.ext rfl

@[simp] theorem fullyFaithfulNestedDomain_preimage_restriction (f : d ⟶ e)
    {U V : Domain K d.algebra}
    (k : (nestedDomainFunctor f).obj U ⟶ (nestedDomainFunctor f).obj V) :
    ((fullyFaithfulNestedDomain f).preimage k).restriction = k.restriction := rfl

instance (f : d ⟶ e) : (nestedDomainFunctor f).Full :=
  (fullyFaithfulNestedDomain f).full

instance (f : d ⟶ e) : (nestedDomainFunctor f).Faithful :=
  (fullyFaithfulNestedDomain f).faithful

/-- The identity chart inclusion changes no represented algebra or base map. -/
def nestedDomainIdIso (d : RationalChart K A) (U : Domain K d.algebra) :
    nestedDomain (𝟙 d) U ≅ U where
  hom := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

/-- Successive nested transport agrees with transport through the composite;
both actual comparison maps are identities on the retained domain algebra. -/
def nestedDomainCompIso (f : d ⟶ e) (g : e ⟶ h) (U : Domain K d.algebra) :
    nestedDomain g (nestedDomain f U) ≅ nestedDomain (f ≫ g) U where
  hom := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  inv := ⟨BoundedAlgHom.id K U.algebra, rfl⟩
  hom_inv_id := Domain.Inclusion.ext rfl
  inv_hom_id := Domain.Inclusion.ext rfl

@[simp] theorem nestedDomainIdIso_hom_restriction (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (nestedDomainIdIso d U).hom.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem nestedDomainIdIso_inv_restriction (d : RationalChart K A)
    (U : Domain K d.algebra) :
    (nestedDomainIdIso d U).inv.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem nestedDomainCompIso_hom_restriction (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) :
    (nestedDomainCompIso f g U).hom.restriction = BoundedAlgHom.id K U.algebra := rfl

@[simp] theorem nestedDomainCompIso_inv_restriction (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) :
    (nestedDomainCompIso f g U).inv.restriction = BoundedAlgHom.id K U.algebra := rfl

/-- Identity and composite comparisons are actual natural isomorphisms. -/
def nestedDomainIdNatIso (d : RationalChart K A) :
    nestedDomainFunctor (𝟙 d) ≅ 𝟭 (Domain K d.algebra) :=
  NatIso.ofComponents (nestedDomainIdIso d)
    (by intro U V k; apply Domain.Inclusion.ext; rfl)

def nestedDomainCompNatIso (f : d ⟶ e) (g : e ⟶ h) :
    nestedDomainFunctor f ⋙ nestedDomainFunctor g ≅ nestedDomainFunctor (f ≫ g) :=
  NatIso.ofComponents (nestedDomainCompIso f g)
    (by intro U V k; apply Domain.Inclusion.ext; rfl)

/-- The two identity-comparison paths retain the same bounded restriction. -/
theorem nestedDomainCompIso_source_id (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedDomainCompIso (𝟙 d) f U).hom =
      (nestedDomainFunctor f).map (nestedDomainIdIso d U).hom := by
  apply Domain.Inclusion.ext
  rfl

theorem nestedDomainCompIso_target_id (f : d ⟶ e) (U : Domain K d.algebra) :
    (nestedDomainCompIso f (𝟙 e) U).hom =
      (nestedDomainIdIso e (nestedDomain f U)).hom := by
  apply Domain.Inclusion.ext
  rfl

/-- Both routes from three successive nested domains to the domain of the
composite are the actual identity bounded map on the retained algebra. -/
theorem nestedDomainCompIso_assoc (f : d ⟶ e) (g : e ⟶ h) (k : h ⟶ j)
    (U : Domain K d.algebra) :
    (nestedDomainFunctor k).map (nestedDomainCompIso f g U).hom ≫
        (nestedDomainCompIso (f ≫ g) k U).hom =
      (nestedDomainCompIso g k (nestedDomain f U)).hom ≫
        (nestedDomainCompIso f (g ≫ k) U).hom := by
  apply Domain.Inclusion.ext
  rfl

/-- Ambient extension compares successive and direct nested transport by
the same actual maps. -/
theorem extendNestedDomainIso_comp (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) :
    (extendNestedDomainIso g (nestedDomain f U)).hom ≫
        (extendNestedDomainIso f U).hom =
      h.extendDomainFunctor.map (nestedDomainCompIso f g U).hom ≫
        (extendNestedDomainIso (f ≫ g) U).hom := by
  apply Domain.Inclusion.ext
  rfl

/-- The identity comparison is also the identity on actual locus points. -/
theorem nestedDomainLocusHomeomorph_id (d : RationalChart K A)
    (U : Domain K d.algebra) (x : U.locus) :
    (nestedDomainIdIso d U).hom.locusMap
        (nestedDomainLocusHomeomorph (𝟙 d) U x) = x := by
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- Successive locus homeomorphisms equal the composite comparison on
actual spectrum points. -/
theorem nestedDomainLocusHomeomorph_comp (f : d ⟶ e) (g : e ⟶ h)
    (U : Domain K d.algebra) (x : U.locus) :
    (nestedDomainCompIso f g U).hom.locusMap
        (nestedDomainLocusHomeomorph g (nestedDomain f U)
          (nestedDomainLocusHomeomorph f U x)) =
      nestedDomainLocusHomeomorph (f ≫ g) U x := by
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro a
  rfl

/-- The actual affinoid-space and spectrum diagrams are retained. -/
theorem nestedDomainFunctor_comp_toAffinoidSpace (f : d ⟶ e) :
    nestedDomainFunctor f ⋙ Domain.toAffinoidSpace K e.algebra =
      Domain.toAffinoidSpace K d.algebra := rfl

theorem nestedDomainFunctor_comp_toTopologicalSpace (f : d ⟶ e) :
    nestedDomainFunctor f ⋙ Domain.toTopologicalSpace K e.algebra =
      Domain.toTopologicalSpace K d.algebra := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
