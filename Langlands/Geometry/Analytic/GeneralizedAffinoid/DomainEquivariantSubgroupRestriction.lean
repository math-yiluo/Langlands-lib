import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEquivariantGluing
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantSubgroupRestriction

/-! # Subgroup restriction of represented-locus actions and equivariant maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- Restricting a locus operator retains the same ambient spectrum action. -/
theorem invariantLocusOperator_subgroup {J H : OpenSubgroup G} (h : J ≤ H)
    (d : ρ.InvariantDomain H) (g : J) :
    ρ.invariantLocusOperator J ((ρ.invariantDomainRestriction h).obj d) g =
      ρ.invariantLocusOperator H d (openSubgroupInclusion h g) :=
  rfl

/-- The entire represented-locus diagram commutes with subgroup restriction. -/
theorem invariantLocusActionFunctor_subgroup {J H : OpenSubgroup G} (h : J ≤ H) :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantLocusActionFunctor J =
      ρ.invariantLocusActionFunctor H ⋙
        Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom :=
  rfl

/-- Restriction preserves the actual structural quotient and its equivariance. -/
theorem invariantSpectrumToLocus_subgroup {J H : OpenSubgroup G} (h : J ≤ H)
    (d : ρ.InvariantDomain H) :
    ρ.invariantSpectrumToLocus J ((ρ.invariantDomainRestriction h).obj d) =
      (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).map
        (ρ.invariantSpectrumToLocus H d) :=
  rfl

/-- An equivariant continuous map remains equivariant for a smaller open
subgroup, with its source representation and target space unchanged. -/
def equivariantLocusMapRestriction {J H : OpenSubgroup G} (h : J ≤ H)
    {d : ρ.InvariantDomain H} {Y : Action TopCat.{w} H}
    (f : ρ.EquivariantLocusMap H d Y) :
    ρ.EquivariantLocusMap J ((ρ.invariantDomainRestriction h).obj d)
      ((Action.res TopCat.{w} (openSubgroupInclusion h).toMonoidHom).obj Y) :=
  ⟨f.val, fun g x => f.property (openSubgroupInclusion h g) x⟩

@[simp]
theorem equivariantLocusMapRestriction_val {J H : OpenSubgroup G} (h : J ≤ H)
    {d : ρ.InvariantDomain H} {Y : Action TopCat.{w} H}
    (f : ρ.EquivariantLocusMap H d Y) :
    (ρ.equivariantLocusMapRestriction h f).val = f.val :=
  rfl

@[simp]
theorem equivariantLocusMapRestriction_refl (H : OpenSubgroup G)
    {d : ρ.InvariantDomain H} {Y : Action TopCat.{w} H}
    (f : ρ.EquivariantLocusMap H d Y) :
    ρ.equivariantLocusMapRestriction (le_refl H) f = f :=
  rfl

/-- Successive subgroup restriction agrees with direct restriction. -/
@[simp]
theorem equivariantLocusMapRestriction_comp {I J H : OpenSubgroup G}
    (hIJ : I ≤ J) (hJH : J ≤ H)
    {d : ρ.InvariantDomain H} {Y : Action TopCat.{w} H}
    (f : ρ.EquivariantLocusMap H d Y) :
    ρ.equivariantLocusMapRestriction hIJ
        (ρ.equivariantLocusMapRestriction hJH f) =
      ρ.equivariantLocusMapRestriction (hIJ.trans hJH) f :=
  rfl

/-- Changing the acting subgroup commutes with equivariant target maps. -/
theorem equivariantLocusMapRestriction_postcomp {J H : OpenSubgroup G} (h : J ≤ H)
    {d : ρ.InvariantDomain H} {Y Z : Action TopCat.{w} H}
    (p : Y ⟶ Z) (f : ρ.EquivariantLocusMap H d Y) :
    ρ.equivariantLocusMapRestriction h (ρ.equivariantLocusMapPostcomp p f) =
      ρ.equivariantLocusMapPostcomp
        ((Action.res TopCat.{w} (openSubgroupInclusion h).toMonoidHom).map p)
        (ρ.equivariantLocusMapRestriction h f) :=
  rfl

/-- In the common space universe this is precisely Mathlib's restriction of
action-category morphisms, including the same continuous underlying map. -/
theorem equivariantLocusMapHomEquiv_subgroup {J H : OpenSubgroup G} (h : J ≤ H)
    {d : ρ.InvariantDomain H} {Y : Action TopCat.{u} H}
    (f : ρ.invariantLocusAction H d ⟶ Y) :
    ρ.equivariantLocusMapRestriction h (ρ.equivariantLocusMapHomEquiv H d Y f) =
      ρ.equivariantLocusMapHomEquiv J ((ρ.invariantDomainRestriction h).obj d)
        ((Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).obj Y)
        ((Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).map f) :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
