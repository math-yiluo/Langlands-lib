import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousFiniteCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEquivariantCoverRefinement

/-! # Actual finite cover refinement diagrams of jointly continuous actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H)

/-- Restrict the proved finite disjoint-union continuity to any preserving
open subgroup, retaining all original component operators. -/
def invariantCoverSpectrum (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) : ContAction TopCat.{u} H :=
  (ContAction.res TopCat.{u} (openSubgroupInclusion
    ((ρ.le_finiteFamilyOpenSubgroup_iff H H c.obj).mpr ⟨le_rfl, hc⟩))).obj
      (ρ.finiteCoverSpectrum H d c)

@[simp]
theorem invariantCoverSpectrum_toAction (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ρ.invariantCoverSpectrum H d c hc).obj =
      ρ.invariantCoverSpectrumAction H d c hc := rfl

@[simp]
theorem invariantCoverSpectrum_mk (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))
    (g : H) (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ConcreteCategory.hom ((ρ.invariantCoverSpectrum H d c hc).obj.ρ g) ⟨i, x⟩ =
      Sigma.mk i (ConcreteCategory.hom
        ((((ρ.invariantSpectrumFunctor H).obj ⟨c.obj i, hc i⟩).obj).ρ g) x) := rfl

/-- Lift the original total quotient at the prescribed preserving subgroup. -/
def invariantCoverQuotientContinuous (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    ρ.invariantCoverSpectrum H d c hc ⟶ (ρ.invariantLocusFunctor H).obj d :=
  ObjectProperty.homMk (ρ.invariantCoverQuotient H d c hc)

@[simp]
theorem invariantCoverQuotientContinuous_toAction (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ρ.invariantCoverQuotientContinuous H d c hc).hom =
      ρ.invariantCoverQuotient H d c hc := rfl

@[simp]
theorem invariantCoverQuotientContinuous_hom (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ρ.invariantCoverQuotientContinuous H d c hc).hom.hom = TopCat.ofHom c.totalMap := rfl

theorem invariantCoverQuotientContinuous_surjective (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    Function.Surjective (ρ.invariantCoverQuotientContinuous H d c hc).hom.hom :=
  c.totalMap_surjective

theorem invariantCoverQuotientContinuous_isClosedMap (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    IsClosedMap (ρ.invariantCoverQuotientContinuous H d c hc).hom.hom :=
  c.totalMap_isClosedMap

theorem invariantCoverQuotientContinuous_isQuotientMap (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    IsQuotientMap (ρ.invariantCoverQuotientContinuous H d c hc).hom.hom :=
  c.totalMap_isQuotientMap

section Refinement

variable {b c : Domain.FiniteCover d.obj}
  (hb : ∀ j, H ≤ ρ.locusOpenSubgroup (b.obj j))
  (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))

/-- The unchanged actual bounded refinement pullback between jointly
continuous finite spectrum actions. -/
def invariantCoverSpectrumMapContinuous (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrum H d b hb ⟶ ρ.invariantCoverSpectrum H d c hc :=
  ObjectProperty.homMk (ρ.invariantCoverSpectrumMap H d hb hc r)

@[simp]
theorem invariantCoverSpectrumMapContinuous_toAction (r : Domain.FiniteCover.Refinement b c) :
    (ρ.invariantCoverSpectrumMapContinuous H d hb hc r).hom =
      ρ.invariantCoverSpectrumMap H d hb hc r := rfl

@[simp]
theorem invariantCoverSpectrumMapContinuous_hom (r : Domain.FiniteCover.Refinement b c) :
    (ρ.invariantCoverSpectrumMapContinuous H d hb hc r).hom.hom =
      TopCat.ofHom r.spectrumMap := rfl

@[simp]
theorem invariantCoverSpectrumMapContinuous_apply (r : Domain.FiniteCover.Refinement b c)
    (j : Fin b.size) (x : BanachSpectrum (b.obj j).algebra) :
    (ρ.invariantCoverSpectrumMapContinuous H d hb hc r).hom.hom ⟨j, x⟩ =
      Sigma.mk (r.index j) ((r.map j).spectrumMap x) := rfl

/-- The original refinement triangle holds in continuous actions. -/
theorem invariantCoverSpectrumMapContinuous_over_target
    (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrumMapContinuous H d hb hc r ≫
        ρ.invariantCoverQuotientContinuous H d c hc =
      ρ.invariantCoverQuotientContinuous H d b hb := by
  apply ObjectProperty.hom_ext _
  exact ρ.invariantCoverSpectrumMap_over_target H d hb hc r

end Refinement

/-- Every original cover and chosen bounded refinement is retained as a
diagram over the jointly continuous action on the actual target locus. -/
def invariantCoverSpectrumContinuousOverFunctor :
    ρ.InvariantFiniteCover H d ⥤ Over ((ρ.invariantLocusFunctor H).obj d) where
  obj c := Over.mk (ρ.invariantCoverQuotientContinuous H d c.obj c.property)
  map {b c} f := Over.homMk
    (ρ.invariantCoverSpectrumMapContinuous H d b.property c.property f.hom)
    (ρ.invariantCoverSpectrumMapContinuous_over_target H d b.property c.property f.hom)
  map_id c := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext _
    exact congrArg (fun f => f.left)
      ((ρ.invariantCoverSpectrumOverFunctor H d).map_id c)
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext _
    exact congrArg (fun f => f.left)
      ((ρ.invariantCoverSpectrumOverFunctor H d).map_comp f g)

@[simp]
theorem invariantCoverSpectrumContinuousOverFunctor_obj_left
    (c : ρ.InvariantFiniteCover H d) :
    ((ρ.invariantCoverSpectrumContinuousOverFunctor H d).obj c).left =
      ρ.invariantCoverSpectrum H d c.obj c.property := rfl

@[simp]
theorem invariantCoverSpectrumContinuousOverFunctor_obj_hom
    (c : ρ.InvariantFiniteCover H d) :
    ((ρ.invariantCoverSpectrumContinuousOverFunctor H d).obj c).hom =
      ρ.invariantCoverQuotientContinuous H d c.obj c.property := rfl

@[simp]
theorem invariantCoverSpectrumContinuousOverFunctor_map_left
    {b c : ρ.InvariantFiniteCover H d} (f : b ⟶ c) :
    ((ρ.invariantCoverSpectrumContinuousOverFunctor H d).map f).left =
      ρ.invariantCoverSpectrumMapContinuous H d b.property c.property f.hom := rfl

/-- Forgetting joint continuity recovers the full original overcategory
diagram, including every refinement index and bounded component map. -/
@[simp]
theorem invariantCoverSpectrumContinuousOverFunctor_toAction :
    ρ.invariantCoverSpectrumContinuousOverFunctor H d ⋙
        Over.post (Action.isContinuous TopCat.{u} H).ι =
      ρ.invariantCoverSpectrumOverFunctor H d := rfl

section Subgroup

variable {J : OpenSubgroup G} (h : J ≤ H)

theorem invariantCoverSpectrum_subgroup (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).obj
        (ρ.invariantCoverSpectrum H d c hc) =
      ρ.invariantCoverSpectrum J ((ρ.invariantDomainRestriction h).obj d)
        c (fun i => h.trans (hc i)) := rfl

theorem invariantCoverQuotientContinuous_subgroup (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantCoverQuotientContinuous H d c hc) =
      ρ.invariantCoverQuotientContinuous J ((ρ.invariantDomainRestriction h).obj d)
        c (fun i => h.trans (hc i)) := rfl

theorem invariantCoverSpectrumMapContinuous_subgroup {b c : Domain.FiniteCover d.obj}
    (hb : ∀ j, H ≤ ρ.locusOpenSubgroup (b.obj j))
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))
    (r : Domain.FiniteCover.Refinement b c) :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantCoverSpectrumMapContinuous H d hb hc r) =
      ρ.invariantCoverSpectrumMapContinuous J ((ρ.invariantDomainRestriction h).obj d)
        (fun j => h.trans (hb j)) (fun i => h.trans (hc i)) r := rfl

/-- Subgroup restriction commutes with the complete continuous refinement
diagram over the unchanged represented target locus. -/
theorem invariantCoverSpectrumContinuousOverFunctor_subgroup :
    ρ.invariantCoverRestriction H d h ⋙
        ρ.invariantCoverSpectrumContinuousOverFunctor J
          ((ρ.invariantDomainRestriction h).obj d) =
      ρ.invariantCoverSpectrumContinuousOverFunctor H d ⋙
        Over.post (ContAction.res TopCat.{u} (openSubgroupInclusion h)) := rfl

end Subgroup

/-- An arbitrary actual refinement has a continuous equivariant spectrum
map at the constructed common open stabilizer of both original covers. -/
def commonCoverSpectrumMapContinuous (c b : Domain.FiniteCover d.obj)
    (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrum (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        b (ρ.commonCoverOpenSubgroup_stabilizes_right H c b) ⟶
      ρ.invariantCoverSpectrum (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        c (ρ.commonCoverOpenSubgroup_stabilizes_left H c b) :=
  ρ.invariantCoverSpectrumMapContinuous (ρ.commonCoverOpenSubgroup H c b)
    ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
    (ρ.commonCoverOpenSubgroup_stabilizes_right H c b)
    (ρ.commonCoverOpenSubgroup_stabilizes_left H c b) r

@[simp]
theorem commonCoverSpectrumMapContinuous_hom (c b : Domain.FiniteCover d.obj)
    (r : Domain.FiniteCover.Refinement b c) :
    (ρ.commonCoverSpectrumMapContinuous H d c b r).hom.hom =
      TopCat.ofHom r.spectrumMap := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
