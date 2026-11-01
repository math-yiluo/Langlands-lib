import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantActions
import Langlands.Geometry.Analytic.StrictTestDomain.InvariantSubgroupRestriction

/-! # Subgroup restriction of continuous weighted rational diagrams -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- A chart preserved by J is preserved by H whenever H is contained in J.
All original bounded restriction maps are retained. -/
def normInvariantChartRestriction {H J : OpenSubgroup G} (h : H ≤ J) :
    NormInvariantChart ρ hρ J ⥤ NormInvariantChart ρ hρ H :=
  ObjectProperty.ιOfLE (fun _ hd => h.trans hd)

/-- Subgroup restriction is the full inclusion on the unchanged chart homs. -/
def normInvariantChartRestrictionFullyFaithful {H J : OpenSubgroup G} (h : H ≤ J) :
    (normInvariantChartRestriction ρ hρ h).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

instance {H J : OpenSubgroup G} (h : H ≤ J) :
    (normInvariantChartRestriction ρ hρ h).Full :=
  (normInvariantChartRestrictionFullyFaithful ρ hρ h).full

instance {H J : OpenSubgroup G} (h : H ≤ J) :
    (normInvariantChartRestriction ρ hρ h).Faithful :=
  (normInvariantChartRestrictionFullyFaithful ρ hρ h).faithful

@[simp]
theorem normInvariantChartRestriction_obj {H J : OpenSubgroup G} (h : H ≤ J)
    (d : NormInvariantChart ρ hρ J) :
    ((normInvariantChartRestriction ρ hρ h).obj d).obj = d.obj := rfl

@[simp]
theorem normInvariantChartRestriction_map {H J : OpenSubgroup G} (h : H ≤ J)
    {d e : NormInvariantChart ρ hρ J} (f : d ⟶ e) :
    ((normInvariantChartRestriction ρ hρ h).map f).hom = f.hom := rfl

@[simp]
theorem normInvariantChartRestriction_forget {H J : OpenSubgroup G} (h : H ≤ J) :
    normInvariantChartRestriction ρ hρ h ⋙ (normInvariantChartProperty ρ hρ H).ι =
      (normInvariantChartProperty ρ hρ J).ι := rfl

@[simp]
theorem normInvariantChartRestriction_refl (H : OpenSubgroup G) :
    normInvariantChartRestriction ρ hρ (le_refl H) =
      𝟭 (NormInvariantChart ρ hρ H) := rfl

@[simp]
theorem normInvariantChartRestriction_comp {H I J : OpenSubgroup G}
    (hHI : H ≤ I) (hIJ : I ≤ J) :
    normInvariantChartRestriction ρ hρ hIJ ⋙ normInvariantChartRestriction ρ hρ hHI =
      normInvariantChartRestriction ρ hρ (hHI.trans hIJ) := rfl

/-- Both routes to the full local stabilizer are the same continuous
homomorphism with the original subgroup topologies. -/
theorem normInvariantStabilizerInclusion_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : NormInvariantChart ρ hρ J) :
    normInvariantStabilizerInclusion ρ hρ H
        ((normInvariantChartRestriction ρ hρ h).obj d) =
      (normInvariantStabilizerInclusion ρ hρ J d).comp (openSubgroupInclusion h) := rfl

/-- The actual jointly continuous locus action restricts without changing its
space or ambient point operators. -/
theorem normInvariantLocusAction_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : NormInvariantChart ρ hρ J) :
    normInvariantLocusAction ρ hρ H ((normInvariantChartRestriction ρ hρ h).obj d) =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).obj
        (normInvariantLocusAction ρ hρ J d) := rfl

/-- Every original locus inclusion is retained in the restricted diagram. -/
theorem normInvariantLocusFunctor_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    normInvariantChartRestriction ρ hρ h ⋙ normInvariantLocusFunctor ρ hρ H =
      normInvariantLocusFunctor ρ hρ J ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

variable [CompleteSpace K]

/-- Restricting the common subgroup keeps the entire quotient-norm continuous
section action, including its bounded operators and inverses. -/
theorem normInvariantSectionAction_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : NormInvariantChart ρ hρ J) :
    normInvariantSectionAction ρ hρ H ((normInvariantChartRestriction ρ hρ h).obj d) =
      (NormContinuousAction.restrict (openSubgroupInclusion h)).obj
        (normInvariantSectionAction ρ hρ J d) := rfl

/-- The full bounded automorphism homomorphism restricts along H to J. -/
theorem normInvariantSectionAction_actionAut_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) (d : NormInvariantChart ρ hρ J) :
    (normInvariantSectionAction ρ hρ H
        ((normInvariantChartRestriction ρ hρ h).obj d)).actionAut =
      (normInvariantSectionAction ρ hρ J d).actionAut.comp
        (openSubgroupInclusion h).toMonoidHom := rfl

/-- Restriction of chart indices and restriction of the continuous acting
group commute for the full bounded section presheaf. -/
theorem normInvariantBoundedPresheaf_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    (normInvariantChartRestriction ρ hρ h).op ⋙ normInvariantBoundedPresheaf ρ hρ H =
      normInvariantBoundedPresheaf ρ hρ J ⋙
        NormContinuousAction.restrict (openSubgroupInclusion h) := rfl

/-- The equivariant structural bounded base map is unchanged by subgroup
restriction, including its source action. -/
theorem normInvariantBaseMapNat_app_subgroup {H J : OpenSubgroup G} (h : H ≤ J)
    (d : (NormInvariantChart ρ hρ J)ᵒᵖ) :
    (normInvariantBaseMapNat ρ hρ H).app
        ((normInvariantChartRestriction ρ hρ h).op.obj d) =
      (NormContinuousAction.restrict (openSubgroupInclusion h)).map
        ((normInvariantBaseMapNat ρ hρ J).app d) := rfl

local instance (H : OpenSubgroup G) : IsTopologicalGroup H :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)

/-- The jointly continuous spectrum diagram commutes with subgroup
restriction, retaining the inverse pullbacks and bounded restriction maps. -/
theorem normInvariantSpectrumFunctor_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    normInvariantChartRestriction ρ hρ h ⋙ normInvariantSpectrumFunctor ρ hρ H =
      normInvariantSpectrumFunctor ρ hρ J ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

/-- Restrict the natural continuous equivariant rational spectrum-locus
homeomorphism along the continuous subgroup inclusion. -/
def normInvariantSpectrumLocusRestrictionIso {H J : OpenSubgroup G} (h : H ≤ J) :
    normInvariantChartRestriction ρ hρ h ⋙ normInvariantSpectrumFunctor ρ hρ H ≅
      normInvariantChartRestriction ρ hρ h ⋙ normInvariantLocusFunctor ρ hρ H :=
  Functor.isoWhiskerRight (normInvariantSpectrumLocusIso ρ hρ J)
    (ContAction.res TopCat.{u} (openSubgroupInclusion h))

/-- Restricting the acting group or reinterpreting the invariant charts gives
exactly the same equivariant natural homeomorphism. -/
theorem normInvariantSpectrumLocusRestrictionIso_eq {H J : OpenSubgroup G}
    (h : H ≤ J) :
    normInvariantSpectrumLocusRestrictionIso ρ hρ h =
      Functor.isoWhiskerLeft (normInvariantChartRestriction ρ hρ h)
        (normInvariantSpectrumLocusIso ρ hρ H) := rfl

@[simp]
theorem normInvariantSpectrumLocusRestrictionIso_hom_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : NormInvariantChart ρ hρ J)
    (x : BanachSpectrum d.obj.algebra) :
    ((normInvariantSpectrumLocusRestrictionIso ρ hρ h).hom.app d).hom.hom x =
      d.obj.locusHomeomorph x := rfl

@[simp]
theorem normInvariantSpectrumLocusRestrictionIso_inv_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : NormInvariantChart ρ hρ J) (x : d.obj.locus) :
    ((normInvariantSpectrumLocusRestrictionIso ρ hρ h).inv.app d).hom.hom x =
      d.obj.locusHomeomorph.symm x := rfl

/-- Forgetting all actions recovers the original natural rational
homeomorphisms on the unchanged full J-invariant chart category. -/
@[simp]
theorem normInvariantSpectrumLocusRestrictionIso_forget {H J : OpenSubgroup G}
    (h : H ≤ J) :
    Functor.isoWhiskerRight (normInvariantSpectrumLocusRestrictionIso ρ hρ h)
        (forget₂ _ TopCat.{u}) =
      Functor.isoWhiskerLeft (normInvariantChartProperty ρ hρ J).ι
        (spectrumLocusIso K A) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
