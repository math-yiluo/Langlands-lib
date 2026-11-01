import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantActions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantSubgroupRestriction

/-! # Subgroup restriction of represented-domain spectral rational diagrams -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory DomainAutomorphism
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

/-- A chart preserved by J is preserved by H whenever H is contained in J.
All original bounded restriction maps are retained. -/
def spectralInvariantChartRestriction {H J : OpenSubgroup G} (h : H ≤ J) :
    SpectralInvariantChart ρ J ⥤ SpectralInvariantChart ρ H :=
  ObjectProperty.ιOfLE (fun _ hd => h.trans hd)

/-- Subgroup restriction is the full inclusion on the unchanged chart homs. -/
def spectralInvariantChartRestrictionFullyFaithful {H J : OpenSubgroup G} (h : H ≤ J) :
    (spectralInvariantChartRestriction ρ h).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

instance {H J : OpenSubgroup G} (h : H ≤ J) :
    (spectralInvariantChartRestriction ρ h).Full :=
  (spectralInvariantChartRestrictionFullyFaithful ρ h).full

instance {H J : OpenSubgroup G} (h : H ≤ J) :
    (spectralInvariantChartRestriction ρ h).Faithful :=
  (spectralInvariantChartRestrictionFullyFaithful ρ h).faithful

@[simp]
theorem spectralInvariantChartRestriction_obj {H J : OpenSubgroup G} (h : H ≤ J)
    (d : SpectralInvariantChart ρ J) :
    ((spectralInvariantChartRestriction ρ h).obj d).obj = d.obj := rfl

@[simp]
theorem spectralInvariantChartRestriction_map {H J : OpenSubgroup G} (h : H ≤ J)
    {d e : SpectralInvariantChart ρ J} (f : d ⟶ e) :
    ((spectralInvariantChartRestriction ρ h).map f).hom = f.hom := rfl

@[simp]
theorem spectralInvariantChartRestriction_forget {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantChartRestriction ρ h ⋙ (spectralInvariantChartProperty ρ H).ι =
      (spectralInvariantChartProperty ρ J).ι := rfl

@[simp]
theorem spectralInvariantChartRestriction_refl (H : OpenSubgroup G) :
    spectralInvariantChartRestriction ρ (le_refl H) =
      𝟭 (SpectralInvariantChart ρ H) := rfl

@[simp]
theorem spectralInvariantChartRestriction_comp {H I J : OpenSubgroup G}
    (hHI : H ≤ I) (hIJ : I ≤ J) :
    spectralInvariantChartRestriction ρ hIJ ⋙ spectralInvariantChartRestriction ρ hHI =
      spectralInvariantChartRestriction ρ (hHI.trans hIJ) := rfl

/-- The full chart-to-domain inclusion commutes with the existing
restriction of represented-domain diagrams. -/
theorem spectralInvariantDomainFunctor_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantChartRestriction ρ h ⋙ spectralInvariantDomainFunctor ρ H =
      spectralInvariantDomainFunctor ρ J ⋙ ρ.invariantDomainRestriction h := rfl

/-- Both routes to the full local stabilizer are the same continuous
homomorphism with the original subgroup topologies. -/
theorem spectralInvariantStabilizerInclusion_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : SpectralInvariantChart ρ J) :
    spectralInvariantStabilizerInclusion ρ H
        ((spectralInvariantChartRestriction ρ h).obj d) =
      (spectralInvariantStabilizerInclusion ρ J d).comp (openSubgroupInclusion h) := rfl

/-- Every original locus inclusion is retained in the restricted diagram. -/
theorem spectralInvariantLocusFunctor_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantChartRestriction ρ h ⋙ spectralInvariantLocusFunctor ρ H =
      spectralInvariantLocusFunctor ρ J ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

/-- Restricting the common subgroup keeps the entire represented-domain spectral
section action, including its bounded operators and inverses. -/
theorem spectralInvariantSectionAction_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : SpectralInvariantChart ρ J) :
    spectralInvariantSectionAction ρ H ((spectralInvariantChartRestriction ρ h).obj d) =
      (DomainSpectralActionCategory.restrict (openSubgroupInclusion h)).obj
        (spectralInvariantSectionAction ρ J d) := rfl

/-- The full bounded automorphism homomorphism restricts along H to J. -/
theorem spectralInvariantSectionAction_actionAut_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) :
    (spectralInvariantSectionAction ρ H
        ((spectralInvariantChartRestriction ρ h).obj d)).actionAut =
      (spectralInvariantSectionAction ρ J d).actionAut.comp
        (openSubgroupInclusion h).toMonoidHom := rfl

/-- Restriction of chart indices and restriction of the continuous acting
group commute for the full bounded section presheaf. -/
theorem spectralInvariantBoundedPresheaf_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    (spectralInvariantChartRestriction ρ h).op ⋙ spectralInvariantBoundedPresheaf ρ H =
      spectralInvariantBoundedPresheaf ρ J ⋙
        DomainSpectralActionCategory.restrict (openSubgroupInclusion h) := rfl

/-- The source of every structural bounded map restricts by the same
continuous inclusion, keeping the original ambient algebra and action. -/
theorem spectralInvariantBaseAction_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantBaseAction ρ H =
      (DomainSpectralActionCategory.restrict (openSubgroupInclusion h)).obj
        (spectralInvariantBaseAction ρ J) := rfl

/-- The equivariant structural bounded base map is unchanged by subgroup
restriction, including its source action. -/
theorem spectralInvariantBaseMapNat_app_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : (SpectralInvariantChart ρ J)ᵒᵖ) :
    (spectralInvariantBaseMapNat ρ H).app
        ((spectralInvariantChartRestriction ρ h).op.obj d) =
      (DomainSpectralActionCategory.restrict (openSubgroupInclusion h)).map
        ((spectralInvariantBaseMapNat ρ J).app d) := rfl

/-- The jointly continuous spectrum diagram commutes with subgroup
restriction, retaining the inverse pullbacks and bounded restriction maps. -/
theorem spectralInvariantSpectrumFunctor_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantChartRestriction ρ h ⋙ spectralInvariantSpectrumFunctor ρ H =
      spectralInvariantSpectrumFunctor ρ J ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

/-- The continuous ambient spectrum action restricts without changing
the spectrum or its inverse-pullback operators. -/
theorem spectralInvariantGlobalSpectrum_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    ρ.restrictedGlobalSpectrum H =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).obj
        (ρ.restrictedGlobalSpectrum J) := rfl

/-- The structural spectrum pullback over the ambient algebra is unchanged. -/
theorem spectralInvariantSpectrumToBase_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : SpectralInvariantChart ρ J) :
    spectralInvariantSpectrumToBase ρ H ((spectralInvariantChartRestriction ρ h).obj d) =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (spectralInvariantSpectrumToBase ρ J d) := rfl

/-- Restrict the natural continuous equivariant rational spectrum-locus
homeomorphism along the continuous subgroup inclusion. -/
def spectralInvariantSpectrumLocusRestrictionIso {H J : OpenSubgroup G} (h : H ≤ J) :
    spectralInvariantChartRestriction ρ h ⋙ spectralInvariantSpectrumFunctor ρ H ≅
      spectralInvariantChartRestriction ρ h ⋙ spectralInvariantLocusFunctor ρ H :=
  Functor.isoWhiskerRight (spectralInvariantSpectrumLocusIso ρ J)
    (ContAction.res TopCat.{u} (openSubgroupInclusion h))

/-- Restricting the acting group or reinterpreting the invariant charts gives
exactly the same equivariant natural homeomorphism. -/
theorem spectralInvariantSpectrumLocusRestrictionIso_eq {H J : OpenSubgroup G}
    (h : H ≤ J) :
    spectralInvariantSpectrumLocusRestrictionIso ρ h =
      Functor.isoWhiskerLeft (spectralInvariantChartRestriction ρ h)
        (spectralInvariantSpectrumLocusIso ρ H) := rfl

@[simp]
theorem spectralInvariantSpectrumLocusRestrictionIso_hom_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J)
    (x : BanachSpectrum d.obj.algebra) :
    ((spectralInvariantSpectrumLocusRestrictionIso ρ h).hom.app d).hom.hom x =
      d.obj.locusHomeomorph x := rfl

@[simp]
theorem spectralInvariantSpectrumLocusRestrictionIso_inv_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) (x : d.obj.locus) :
    ((spectralInvariantSpectrumLocusRestrictionIso ρ h).inv.app d).hom.hom x =
      d.obj.locusHomeomorph.symm x := rfl

/-- Forgetting all actions recovers the original natural rational
homeomorphisms on the unchanged full J-invariant chart category. -/
@[simp]
theorem spectralInvariantSpectrumLocusRestrictionIso_forget {H J : OpenSubgroup G}
    (h : H ≤ J) :
    Functor.isoWhiskerRight (spectralInvariantSpectrumLocusRestrictionIso ρ h)
        (forget₂ _ TopCat.{u}) =
      Functor.isoWhiskerLeft (spectralInvariantChartProperty ρ J).ι
        (spectrumLocusIso K A) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
