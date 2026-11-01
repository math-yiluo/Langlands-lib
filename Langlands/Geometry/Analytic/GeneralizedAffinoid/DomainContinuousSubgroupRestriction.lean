import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousOverBase
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEquivariantSubgroupRestriction

/-! # Subgroup compatibility of continuous represented-domain diagrams -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P) {J H : OpenSubgroup G} (h : J ≤ H)

/-- The full actual spectrum diagram commutes with continuous subgroup restriction. -/
theorem invariantSpectrumFunctor_subgroup :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantSpectrumFunctor J =
      ρ.invariantSpectrumFunctor H ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

/-- The full actual locus diagram commutes with continuous subgroup restriction. -/
theorem invariantLocusFunctor_subgroup :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantLocusFunctor J =
      ρ.invariantLocusFunctor H ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) := rfl

/-- Successive restriction retains the original global continuous spectrum action. -/
theorem restrictedGlobalSpectrum_subgroup :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).obj
        (ρ.restrictedGlobalSpectrum H) =
      ρ.restrictedGlobalSpectrum J := rfl

/-- Each bounded structural pullback is unchanged by subgroup restriction. -/
theorem invariantSpectrumToBase_subgroup (d : ρ.InvariantDomain H) :
    ρ.invariantSpectrumToBase J ((ρ.invariantDomainRestriction h).obj d) =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantSpectrumToBase H d) := rfl

/-- The actual inclusion of the represented locus is unchanged. -/
theorem invariantLocusToBase_subgroup (d : ρ.InvariantDomain H) :
    ρ.invariantLocusToBase J ((ρ.invariantDomainRestriction h).obj d) =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantLocusToBase H d) := rfl

/-- The structural quotient remains the same morphism of continuous actions. -/
theorem invariantSpectrumToLocusContinuous_subgroup (d : ρ.InvariantDomain H) :
    ρ.invariantSpectrumToLocusContinuous J ((ρ.invariantDomainRestriction h).obj d) =
      (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantSpectrumToLocusContinuous H d) := rfl

/-- Subgroup restriction commutes with the complete structural quotient transformation. -/
theorem invariantSpectrumToLocusContinuousNatTrans_subgroup :
    Functor.whiskerLeft (ρ.invariantDomainRestriction h)
        (ρ.invariantSpectrumToLocusContinuousNatTrans J) =
      Functor.whiskerRight (ρ.invariantSpectrumToLocusContinuousNatTrans H)
        (ContAction.res TopCat.{u} (openSubgroupInclusion h)) := rfl

/-- The entire spectrum diagram over the unchanged base commutes with restriction. -/
theorem invariantSpectrumOverFunctor_subgroup :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantSpectrumOverFunctor J =
      ρ.invariantSpectrumOverFunctor H ⋙
        Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h)) := rfl

/-- The entire locus diagram over the same base commutes with restriction. -/
theorem invariantLocusOverFunctor_subgroup :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantLocusOverFunctor J =
      ρ.invariantLocusOverFunctor H ⋙
        Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h)) := rfl

/-- Restriction preserves the full quotient transformation over the actual base. -/
theorem invariantSpectrumToLocusOverNatTrans_subgroup :
    Functor.whiskerLeft (ρ.invariantDomainRestriction h)
        (ρ.invariantSpectrumToLocusOverNatTrans J) =
      Functor.whiskerRight (ρ.invariantSpectrumToLocusOverNatTrans H)
        (Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h))) := rfl

/-- The exact spectrum identity as a usable natural comparison isomorphism. -/
def invariantSpectrumOverSubgroupIso :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantSpectrumOverFunctor J ≅
      ρ.invariantSpectrumOverFunctor H ⋙
        Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h)) :=
  eqToIso (ρ.invariantSpectrumOverFunctor_subgroup h)

/-- The corresponding natural comparison for actual represented loci. -/
def invariantLocusOverSubgroupIso :
    ρ.invariantDomainRestriction h ⋙ ρ.invariantLocusOverFunctor J ≅
      ρ.invariantLocusOverFunctor H ⋙
        Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h)) :=
  eqToIso (ρ.invariantLocusOverFunctor_subgroup h)

/-- The concrete comparisons retain the entire quotient square over the base. -/
theorem invariantSpectrumToLocusOverSubgroupIso_comm :
    (ρ.invariantSpectrumOverSubgroupIso h).hom ≫
        Functor.whiskerRight (ρ.invariantSpectrumToLocusOverNatTrans H)
          (Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h))) =
      Functor.whiskerLeft (ρ.invariantDomainRestriction h)
          (ρ.invariantSpectrumToLocusOverNatTrans J) ≫
        (ρ.invariantLocusOverSubgroupIso h).hom := by
  ext d
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
