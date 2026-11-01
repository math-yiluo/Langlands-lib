import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEquivariantCoverDescent

/-! # Equivariant actual spectrum maps of finite cover refinements -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)
  (H : OpenSubgroup G) (d : ρ.InvariantDomain H)

/-- Keep the actual finite disjoint union and restrict its existing action to
any supplied open subgroup preserving all its components. -/
def invariantCoverSpectrumAction (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) : Action TopCat.{u} H :=
  (Action.res TopCat.{u} (openSubgroupInclusion
    ((ρ.le_finiteFamilyOpenSubgroup_iff H H c.obj).mpr ⟨le_rfl, hc⟩)).toMonoidHom).obj
      (ρ.finiteCoverSpectrumAction H d c)

@[simp]
theorem invariantCoverSpectrumAction_mk (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))
    (g : H) (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ConcreteCategory.hom ((ρ.invariantCoverSpectrumAction H d c hc).ρ g) ⟨i, x⟩ =
      Sigma.mk i (ConcreteCategory.hom
        (((ρ.invariantSpectrumActionFunctor H).obj ⟨c.obj i, hc i⟩).ρ g) x) :=
  rfl

/-- The original finite spectrum quotient at the prescribed preserving subgroup. -/
def invariantCoverQuotient (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    ρ.invariantCoverSpectrumAction H d c hc ⟶ ρ.invariantLocusAction H d :=
  (Action.res TopCat.{u} (openSubgroupInclusion
    ((ρ.le_finiteFamilyOpenSubgroup_iff H H c.obj).mpr ⟨le_rfl, hc⟩)).toMonoidHom).map
      (ρ.finiteCoverQuotient H d c)

@[simp]
theorem invariantCoverQuotient_hom (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (ρ.invariantCoverQuotient H d c hc).hom = TopCat.ofHom c.totalMap :=
  rfl

theorem invariantCoverQuotient_isQuotientMap (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    IsQuotientMap (ρ.invariantCoverQuotient H d c hc).hom :=
  c.totalMap_isQuotientMap

section Refinement

variable {b c : Domain.FiniteCover d.obj}
  (hb : ∀ j, H ≤ ρ.locusOpenSubgroup (b.obj j))
  (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))

/-- The continuous map induced by the stored bounded refinement arrows is
equivariant for the constructed component actions. -/
def invariantCoverSpectrumMap (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrumAction H d b hb ⟶
      ρ.invariantCoverSpectrumAction H d c hc where
  hom := TopCat.ofHom r.spectrumMap
  comm g := by
    apply TopCat.ext
    rintro ⟨j, x⟩
    change (Sigma.mk (r.index j)
        ((r.map j).spectrumMap (ConcreteCategory.hom
          (((ρ.invariantSpectrumActionFunctor H).obj ⟨b.obj j, hb j⟩).ρ g) x)) :
        Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) =
      Sigma.mk (r.index j) (ConcreteCategory.hom
        (((ρ.invariantSpectrumActionFunctor H).obj
          ⟨c.obj (r.index j), hc (r.index j)⟩).ρ g) ((r.map j).spectrumMap x))
    exact congrArg (Sigma.mk (β := fun i : Fin c.size =>
        BanachSpectrum (c.obj i).algebra) (r.index j))
      (ConcreteCategory.congr_hom
        (((ρ.invariantSpectrumActionFunctor H).map
          (ObjectProperty.homMk (r.map j) :
            (⟨b.obj j, hb j⟩ : ρ.InvariantDomain H) ⟶
              ⟨c.obj (r.index j), hc (r.index j)⟩)).comm g) x)

@[simp]
theorem invariantCoverSpectrumMap_hom (r : Domain.FiniteCover.Refinement b c) :
    (ρ.invariantCoverSpectrumMap H d hb hc r).hom = TopCat.ofHom r.spectrumMap :=
  rfl

@[simp]
theorem invariantCoverSpectrumMap_apply (r : Domain.FiniteCover.Refinement b c)
    (j : Fin b.size) (x : BanachSpectrum (b.obj j).algebra) :
    (ρ.invariantCoverSpectrumMap H d hb hc r).hom ⟨j, x⟩ =
      Sigma.mk (r.index j) ((r.map j).spectrumMap x) :=
  rfl

/-- Refinement commutes with the actual equivariant quotient maps to the
unchanged target locus. -/
theorem invariantCoverSpectrumMap_over_target (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrumMap H d hb hc r ≫ ρ.invariantCoverQuotient H d c hc =
      ρ.invariantCoverQuotient H d b hb := by
  apply Action.Hom.ext
  exact congrArg TopCat.ofHom r.spectrumMap_over_target

end Refinement

/-- Finite covers whose original component loci are all invariant under H. -/
def invariantCoverProperty : ObjectProperty (Domain.FiniteCover d.obj) :=
  fun c => ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)

/-- The full refinement category retains the original finite covers, index
choices and actual bounded component arrows. -/
abbrev InvariantFiniteCover :=
  (ρ.invariantCoverProperty H d).FullSubcategory

/-- The actual finite spectrum unions form an equivariant diagram over the
original represented target locus. -/
def invariantCoverSpectrumOverFunctor :
    ρ.InvariantFiniteCover H d ⥤ Over (ρ.invariantLocusAction H d) where
  obj c := Over.mk (ρ.invariantCoverQuotient H d c.obj c.property)
  map {b c} f := Over.homMk
    (ρ.invariantCoverSpectrumMap H d b.property c.property f.hom)
    (ρ.invariantCoverSpectrumMap_over_target H d b.property c.property f.hom)
  map_id c := by
    apply Over.OverMorphism.ext
    apply Action.Hom.ext
    apply TopCat.ext
    rintro ⟨i, x⟩
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply Action.Hom.ext
    apply TopCat.ext
    rintro ⟨i, x⟩
    rfl

@[simp]
theorem invariantCoverSpectrumOverFunctor_obj_left (c : ρ.InvariantFiniteCover H d) :
    ((ρ.invariantCoverSpectrumOverFunctor H d).obj c).left =
      ρ.invariantCoverSpectrumAction H d c.obj c.property :=
  rfl

@[simp]
theorem invariantCoverSpectrumOverFunctor_obj_hom (c : ρ.InvariantFiniteCover H d) :
    ((ρ.invariantCoverSpectrumOverFunctor H d).obj c).hom =
      ρ.invariantCoverQuotient H d c.obj c.property :=
  rfl

@[simp]
theorem invariantCoverSpectrumOverFunctor_map_left {b c : ρ.InvariantFiniteCover H d}
    (f : b ⟶ c) :
    ((ρ.invariantCoverSpectrumOverFunctor H d).map f).left =
      ρ.invariantCoverSpectrumMap H d b.property c.property f.hom :=
  rfl

section Subgroup

variable {J : OpenSubgroup G} (h : J ≤ H)

/-- Shrinking the subgroup retains each cover and every chosen refinement. -/
def invariantCoverRestriction :
    ρ.InvariantFiniteCover H d ⥤
      ρ.InvariantFiniteCover J ((ρ.invariantDomainRestriction h).obj d) :=
  ObjectProperty.ιOfLE (fun _ hc i => h.trans (hc i))

/-- The finite disjoint-union actions restrict with identical operators. -/
theorem invariantCoverSpectrumAction_subgroup (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).obj
        (ρ.invariantCoverSpectrumAction H d c hc) =
      ρ.invariantCoverSpectrumAction J ((ρ.invariantDomainRestriction h).obj d)
        c (fun i => h.trans (hc i)) :=
  rfl

/-- Restriction retains the full quotient morphism, including its actual map. -/
theorem invariantCoverQuotient_subgroup (c : Domain.FiniteCover d.obj)
    (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i)) :
    (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom).map
        (ρ.invariantCoverQuotient H d c hc) =
      ρ.invariantCoverQuotient J ((ρ.invariantDomainRestriction h).obj d)
        c (fun i => h.trans (hc i)) :=
  rfl

/-- The complete actual refinement diagram over the locus commutes with
restriction to a smaller open subgroup. -/
theorem invariantCoverSpectrumOverFunctor_subgroup :
    ρ.invariantCoverRestriction H d h ⋙
        ρ.invariantCoverSpectrumOverFunctor J ((ρ.invariantDomainRestriction h).obj d) =
      ρ.invariantCoverSpectrumOverFunctor H d ⋙
        Over.post (Action.res TopCat.{u} (openSubgroupInclusion h).toMonoidHom) :=
  rfl

end Subgroup

/-- Every actual refinement gives an equivariant spectrum map after explicitly
shrinking to the constructed common open subgroup of its two original covers. -/
def commonCoverSpectrumMap (c b : Domain.FiniteCover d.obj)
    (r : Domain.FiniteCover.Refinement b c) :
    ρ.invariantCoverSpectrumAction (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        b (ρ.commonCoverOpenSubgroup_stabilizes_right H c b) ⟶
      ρ.invariantCoverSpectrumAction (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        c (ρ.commonCoverOpenSubgroup_stabilizes_left H c b) :=
  ρ.invariantCoverSpectrumMap (ρ.commonCoverOpenSubgroup H c b)
    ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
    (ρ.commonCoverOpenSubgroup_stabilizes_right H c b)
    (ρ.commonCoverOpenSubgroup_stabilizes_left H c b) r

@[simp]
theorem commonCoverSpectrumMap_hom (c b : Domain.FiniteCover d.obj)
    (r : Domain.FiniteCover.Refinement b c) :
    (ρ.commonCoverSpectrumMap H d c b r).hom = TopCat.ofHom r.spectrumMap :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
