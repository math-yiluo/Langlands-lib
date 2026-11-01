import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantSpectrumOverBase
import Langlands.Geometry.Analytic.StrictTestDomain.InvariantSubgroupRestriction

/-! # Restricting invariant represented-domain diagrams to smaller open subgroups -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

omit [IsTopologicalGroup G] in
@[simp]
theorem openSubgroupInclusion_apply {J H : OpenSubgroup G} (h : J ≤ H) (g : J) :
    ((openSubgroupInclusion h g : H) : G) = (g : G) :=
  rfl

/-- Every domain invariant under H is invariant under its subgroup J. The
functor keeps the actual representation and every bounded restriction. -/
def invariantDomainRestriction {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.InvariantDomain H ⥤ ρ.InvariantDomain J :=
  ObjectProperty.ιOfLE (fun _ hd => h.trans hd)

instance {J H : OpenSubgroup G} (h : J ≤ H) :
    (ρ.invariantDomainRestriction h).Full :=
  (ObjectProperty.fullyFaithfulιOfLE
    (P := ρ.invariantDomainProperty H) (P' := ρ.invariantDomainProperty J)
    (fun _ hd => h.trans hd)).full

instance {J H : OpenSubgroup G} (h : J ≤ H) :
    (ρ.invariantDomainRestriction h).Faithful :=
  (ObjectProperty.fullyFaithfulιOfLE
    (P := ρ.invariantDomainProperty H) (P' := ρ.invariantDomainProperty J)
    (fun _ hd => h.trans hd)).faithful

@[simp]
theorem invariantDomainRestriction_obj {J H : OpenSubgroup G} (h : J ≤ H)
    (d : ρ.InvariantDomain H) :
    ((ρ.invariantDomainRestriction h).obj d).obj = d.obj :=
  rfl

@[simp]
theorem invariantDomainRestriction_map {J H : OpenSubgroup G} (h : J ≤ H)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) :
    ((ρ.invariantDomainRestriction h).map f).hom = f.hom :=
  rfl

/-- Restriction does not alter the full inclusion into actual domain representations. -/
@[simp]
theorem invariantDomainRestriction_forget {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.invariantDomainRestriction h ⋙ (ρ.invariantDomainProperty J).ι =
      (ρ.invariantDomainProperty H).ι :=
  rfl

@[simp]
theorem invariantDomainRestriction_refl (H : OpenSubgroup G) :
    ρ.invariantDomainRestriction (le_refl H) = 𝟭 (ρ.InvariantDomain H) :=
  rfl

@[simp]
theorem invariantDomainRestriction_comp {I J H : OpenSubgroup G}
    (hIJ : I ≤ J) (hJH : J ≤ H) :
    ρ.invariantDomainRestriction hJH ⋙ ρ.invariantDomainRestriction hIJ =
      ρ.invariantDomainRestriction (hIJ.trans hJH) :=
  rfl

/-- Restricting the domain's bounded automorphisms is equality of the entire
constructed action homomorphism, including its inverse maps. -/
theorem invariantSectionAction_subgroup {J H : OpenSubgroup G} (h : J ≤ H)
    (d : ρ.InvariantDomain H) :
    ρ.invariantSectionAction J ((ρ.invariantDomainRestriction h).obj d) =
      (ρ.invariantSectionAction H d).comp (openSubgroupInclusion h).toMonoidHom :=
  rfl

/-- Restriction of the actual geometric affinoid diagram commutes with
restriction of the acting open subgroup. -/
theorem invariantAffinoidActionFunctor_subgroup {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantAffinoidActionFunctor J =
      ρ.invariantAffinoidActionFunctor H ⋙
        Action.res (PresentedAffinoidSpace K) (openSubgroupInclusion h).toMonoidHom :=
  rfl

/-- The same identity retains all spectrum spaces, inverse-pullback operators
and actual bounded restriction pullbacks. -/
theorem invariantSpectrumActionFunctor_subgroup {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantSpectrumActionFunctor J =
      ρ.invariantSpectrumActionFunctor H ⋙
        Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom :=
  rfl

/-- Restricting the original global action in two steps retains its exact
inverse-pullback operators. -/
theorem restrictedGlobalSpectrumAction_subgroup {J H : OpenSubgroup G} (h : J ≤ H) :
    (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).obj
        (ρ.restrictedGlobalSpectrumAction H) =
      ρ.restrictedGlobalSpectrumAction J :=
  rfl

/-- Each structural spectrum map remains the same equivariant map after
restriction to the smaller acting subgroup. -/
theorem invariantSpectrumActionToBase_subgroup {J H : OpenSubgroup G} (h : J ≤ H)
    (d : ρ.InvariantDomain H) :
    ρ.invariantSpectrumActionToBase J ((ρ.invariantDomainRestriction h).obj d) =
      (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).map
        (ρ.invariantSpectrumActionToBase H d) :=
  rfl

/-- The complete diagram over the original spectrum commutes with subgroup
restriction, retaining its structural and bounded restriction maps. -/
theorem invariantSpectrumActionOverFunctor_subgroup {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantSpectrumActionOverFunctor J =
      ρ.invariantSpectrumActionOverFunctor H ⋙
        Over.post (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom) :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
