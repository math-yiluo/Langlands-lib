import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartSpectralRestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralSpectrumFunctor
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousOverBase

/-! # Rational section diagrams for represented-domain spectral actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory DomainAutomorphism

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

/-- Every element of the common subgroup preserves the actual rational locus. -/
def spectralInvariantChartProperty (H : OpenSubgroup G) :
    ObjectProperty (RationalChart K A) :=
  fun d => H ≤ ρ.locusOpenSubgroup d.toDomain

/-- The full category retains every original bounded rational restriction. -/
abbrev SpectralInvariantChart (H : OpenSubgroup G) :=
  (spectralInvariantChartProperty ρ H).FullSubcategory

/-- Include rational charts in the previously constructed invariant full domains. -/
def spectralInvariantDomainFunctor (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ ρ.InvariantDomain H where
  obj d := ⟨d.obj.toDomain, d.property⟩
  map f := ObjectProperty.homMk ((toDomainFunctor K A).map f.hom)
  map_id _ := by
    apply ObjectProperty.hom_ext _
    exact Domain.Inclusion.ext rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext _
    exact Domain.Inclusion.ext rfl

/-- Full faithfulness keeps the bounded map and its equation over A. -/
def fullyFaithfulSpectralInvariantDomain (H : OpenSubgroup G) :
    (spectralInvariantDomainFunctor ρ H).FullyFaithful where
  preimage f := ObjectProperty.homMk ((fullyFaithfulToDomain K A).preimage f.hom)
  map_preimage _ := by
    apply ObjectProperty.hom_ext _
    exact Domain.Inclusion.ext rfl
  preimage_map _ := by
    apply ObjectProperty.hom_ext _
    exact Restriction.ext rfl

instance (H : OpenSubgroup G) : (spectralInvariantDomainFunctor ρ H).Full :=
  (fullyFaithfulSpectralInvariantDomain ρ H).full

instance (H : OpenSubgroup G) : (spectralInvariantDomainFunctor ρ H).Faithful :=
  (fullyFaithfulSpectralInvariantDomain ρ H).faithful

/-- The original common-group inclusion, with the induced subgroup topologies. -/
def spectralInvariantStabilizerInclusion (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) : H →ₜ* ρ.locusOpenSubgroup d.obj.toDomain :=
  ρ.invariantStabilizerInclusion H ((spectralInvariantDomainFunctor ρ H).obj d)

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- Restrict the proved rational spectral action to the common open subgroup. -/
def spectralInvariantSectionAction (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) : DomainSpectralActionCategory K H :=
  DomainSpectralActionCategory.ofDomainSpectralAction
    ((d.obj.restrictSpectralAction ρ).precomp
      (spectralInvariantStabilizerInclusion ρ H d).toMonoidHom
      (spectralInvariantStabilizerInclusion ρ H d).continuous)

@[simp] theorem spectralInvariantSectionAction_algebra (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSectionAction ρ H d).obj.V = d.obj.algebra := rfl

/-- Equality of the full automorphism homomorphisms, including bounded inverses. -/
@[simp] theorem spectralInvariantSectionAction_actionAut (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSectionAction ρ H d).actionAut =
      ρ.invariantSectionAction H ((spectralInvariantDomainFunctor ρ H).obj d) := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  rfl

@[simp] theorem spectralInvariantSectionAction_baseMap (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (g : H) (a : A) :
    ((spectralInvariantSectionAction ρ H d).obj.ρ g).toAlgHom (d.obj.baseMap a) =
      d.obj.baseMap ((ρ.toMonoidHom (g : G)).hom.toAlgHom a) :=
  ρ.invariantSectionAction_baseMap H ((spectralInvariantDomainFunctor ρ H).obj d) g a

/-- Every original bounded rational restriction is automatically equivariant. -/
theorem spectralInvariantSectionAction_restriction (H : OpenSubgroup G)
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e) (g : H) :
    f.hom.restriction.comp ((spectralInvariantSectionAction ρ H e).obj.ρ g) =
      ((spectralInvariantSectionAction ρ H d).obj.ρ g).comp f.hom.restriction :=
  ρ.invariantSectionAction_restriction H ((spectralInvariantDomainFunctor ρ H).map f) g

/-- The original bounded section presheaf takes values in continuous spectral
algebra actions without adding any condition to its bounded arrows. -/
def spectralInvariantBoundedPresheaf (H : OpenSubgroup G) :
    (SpectralInvariantChart ρ H)ᵒᵖ ⥤ DomainSpectralActionCategory K H where
  obj d := spectralInvariantSectionAction ρ H d.unop
  map f := DomainSpectralActionCategory.homMk f.unop.hom.restriction
    (spectralInvariantSectionAction_restriction ρ H f.unop)
  map_id _ := by
    apply DomainSpectralActionCategory.hom_ext
    rfl
  map_comp _ _ := by
    apply DomainSpectralActionCategory.hom_ext
    rfl

@[simp] theorem spectralInvariantBoundedPresheaf_forget (H : OpenSubgroup G) :
    spectralInvariantBoundedPresheaf ρ H ⋙ DomainSpectralActionCategory.forget =
      (spectralInvariantChartProperty ρ H).ι.op ⋙ boundedPresheaf K A := rfl

/-- The unchanged base spectral action restricted to the common subgroup. -/
def spectralInvariantBaseAction (H : OpenSubgroup G) : DomainSpectralActionCategory K H :=
  (DomainSpectralActionCategory.restrict
    { toMonoidHom := H.toSubgroup.subtype
      continuous_toFun := continuous_subtype_val }).obj
    (DomainSpectralActionCategory.ofDomainSpectralAction ρ)

/-- All original structural bounded base maps are a natural equivariant family. -/
def spectralInvariantBaseMapNat (H : OpenSubgroup G) :
    (Functor.const (SpectralInvariantChart ρ H)ᵒᵖ).obj
      (spectralInvariantBaseAction ρ H) ⟶ spectralInvariantBoundedPresheaf ρ H where
  app d := DomainSpectralActionCategory.homMk d.unop.obj.baseMap
    (fun g => BoundedAlgHom.ext
      (fun a => (spectralInvariantSectionAction_baseMap ρ H d.unop g a).symm))
  naturality _ _ f := by
    apply DomainSpectralActionCategory.hom_ext
    exact f.unop.hom.comp_baseMap.symm

/-- Apply the existing continuous spectrum functor to the spectral section diagram. -/
def spectralInvariantSpectrumFunctor (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ ContAction TopCat.{u} H :=
  (spectralInvariantBoundedPresheaf ρ H).rightOp ⋙
    DomainSpectralActionCategory.spectrumFunctor

@[simp] theorem spectralInvariantSpectrumFunctor_obj_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (g : H)
    (x : BanachSpectrum d.obj.algebra) (b : d.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (((spectralInvariantSpectrumFunctor ρ H).obj d).obj.ρ g) x) b =
        x ((ρ.invariantSectionAction H
          ((spectralInvariantDomainFunctor ρ H).obj d) g).inv.toAlgHom b) := by
  change x (((spectralInvariantSectionAction ρ H d).actionAut g).inv.toAlgHom b) = _
  rw [spectralInvariantSectionAction_actionAut]
  rfl

@[simp] theorem spectralInvariantSpectrumFunctor_map_apply (H : OpenSubgroup G)
    {d e : SpectralInvariantChart ρ H} (f : d ⟶ e)
    (x : BanachSpectrum d.obj.algebra) (b : e.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (((spectralInvariantSpectrumFunctor ρ H).map f).hom.hom x) b =
        x (f.hom.restriction b) := rfl

@[simp] theorem spectralInvariantSpectrumFunctor_forget (H : OpenSubgroup G) :
    spectralInvariantSpectrumFunctor ρ H ⋙ forget₂ _ TopCat.{u} =
      (spectralInvariantChartProperty ρ H).ι ⋙ toTopologicalSpace K A := rfl

/-- The two continuous spectrum actions have the same points and operators. -/
def spectralInvariantSpectrumDomainIsoApp (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSpectrumFunctor ρ H).obj d ≅
      (ρ.invariantSpectrumFunctor H).obj ((spectralInvariantDomainFunctor ρ H).obj d) :=
  ObjectProperty.isoMk _
    (Action.mkIso (Iso.refl (TopCat.of (BanachSpectrum d.obj.algebra)))
      (fun g => by
        apply TopCat.ext
        intro x
        change BanachSpectrum.comap
            ((spectralInvariantSectionAction ρ H d).actionAut g).inv.toBoundedRingHom x =
          BanachSpectrum.comap
            (ρ.invariantSectionAction H
              ((spectralInvariantDomainFunctor ρ H).obj d) g).inv.toBoundedRingHom x
        rw [spectralInvariantSectionAction_actionAut]
        rfl))

/-- The spectrum constructed from the spectral section presheaf is naturally
isomorphic to the previous full-domain spectrum diagram, by identity point maps. -/
def spectralInvariantSpectrumDomainIso (H : OpenSubgroup G) :
    spectralInvariantSpectrumFunctor ρ H ≅
      spectralInvariantDomainFunctor ρ H ⋙ ρ.invariantSpectrumFunctor H :=
  NatIso.ofComponents (spectralInvariantSpectrumDomainIsoApp ρ H)
    (fun _ => by
      apply ObjectProperty.hom_ext _
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      rfl)

@[simp] theorem spectralInvariantSpectrumDomainIso_hom_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (x : BanachSpectrum d.obj.algebra) :
    ((spectralInvariantSpectrumDomainIso ρ H).hom.app d).hom.hom x = x := rfl

@[simp] theorem spectralInvariantSpectrumDomainIso_inv_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (x : BanachSpectrum d.obj.algebra) :
    ((spectralInvariantSpectrumDomainIso ρ H).inv.app d).hom.hom x = x := rfl

/-- The actual loci reuse the previously proved continuous full-domain diagram. -/
def spectralInvariantLocusFunctor (H : OpenSubgroup G) :
    SpectralInvariantChart ρ H ⥤ ContAction TopCat.{u} H :=
  spectralInvariantDomainFunctor ρ H ⋙ ρ.invariantLocusFunctor H

@[simp] theorem spectralInvariantLocusFunctor_obj_coe (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (g : H) (x : d.obj.locus) :
    ((show d.obj.locus from
      ConcreteCategory.hom (((spectralInvariantLocusFunctor ρ H).obj d).obj.ρ g) x) :
        BanachSpectrum A) = ρ.toMonoidHom (g : G) • (x : BanachSpectrum A) := rfl

@[simp] theorem spectralInvariantLocusFunctor_forget (H : OpenSubgroup G) :
    spectralInvariantLocusFunctor ρ H ⋙ forget₂ _ TopCat.{u} =
      (spectralInvariantChartProperty ρ H).ι ⋙ locusFunctor K A := rfl

/-- The original rational spectrum homeomorphism intertwines the derived
continuous actions, naturally for every original bounded restriction. -/
def spectralInvariantSpectrumLocusIso (H : OpenSubgroup G) :
    spectralInvariantSpectrumFunctor ρ H ≅ spectralInvariantLocusFunctor ρ H :=
  NatIso.ofComponents (fun d => ObjectProperty.isoMk _
    (Action.mkIso (TopCat.isoOfHomeo d.obj.locusHomeomorph)
      (fun g => by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        change d.obj.spectrumMap
          (BanachSpectrum.comap
            ((spectralInvariantSectionAction ρ H d).actionAut g).inv.toBoundedRingHom x) =
          ρ.toMonoidHom (g : G) • d.obj.spectrumMap x
        rw [spectralInvariantSectionAction_actionAut]
        exact ρ.spectrumMap_smul d.obj.toDomain
          (spectralInvariantStabilizerInclusion ρ H d g) x)))
    (fun f => by
      apply ObjectProperty.hom_ext _
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      exact f.hom.locusHomeomorph_naturality x)

@[simp] theorem spectralInvariantSpectrumLocusIso_forget (H : OpenSubgroup G) :
    Functor.isoWhiskerRight (spectralInvariantSpectrumLocusIso ρ H)
        (forget₂ _ TopCat.{u}) =
      Functor.isoWhiskerLeft (spectralInvariantChartProperty ρ H).ι
        (spectrumLocusIso K A) := rfl

/-- The spectrum-locus isomorphism retains the published structural quotient
transformation after comparison with the original full-domain spectrum action. -/
theorem spectralInvariantSpectrumLocusIso_hom_eq (H : OpenSubgroup G) :
    (spectralInvariantSpectrumLocusIso ρ H).hom =
      (spectralInvariantSpectrumDomainIso ρ H).hom ≫
        Functor.whiskerLeft (spectralInvariantDomainFunctor ρ H)
          (ρ.invariantSpectrumToLocusContinuousNatTrans H) := by
  apply NatTrans.ext
  funext d
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

/-- The continuous structural map has the original bounded spectrum pullback. -/
def spectralInvariantSpectrumToBase (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSpectrumFunctor ρ H).obj d ⟶ ρ.restrictedGlobalSpectrum H :=
  (spectralInvariantSpectrumDomainIso ρ H).hom.app d ≫
    ρ.invariantSpectrumToBase H ((spectralInvariantDomainFunctor ρ H).obj d)

@[simp] theorem spectralInvariantSpectrumToBase_apply (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) (x : BanachSpectrum d.obj.algebra) :
    (spectralInvariantSpectrumToBase ρ H d).hom.hom x = d.obj.spectrumMap x := rfl

/-- The canonical isomorphism commutes with the unchanged ambient base map. -/
theorem spectralInvariantSpectrumLocusIso_over_base (H : OpenSubgroup G)
    (d : SpectralInvariantChart ρ H) :
    (spectralInvariantSpectrumLocusIso ρ H).hom.app d ≫
        ρ.invariantLocusToBase H ((spectralInvariantDomainFunctor ρ H).obj d) =
      spectralInvariantSpectrumToBase ρ H d := by
  apply ObjectProperty.hom_ext _
  apply Action.Hom.ext
  apply TopCat.ext
  intro x
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
