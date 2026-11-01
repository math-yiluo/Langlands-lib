import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEquivariantSubgroupRestriction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverDescent

/-! # Equivariant descent through actual finite cover refinements -/

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

section FixedSubgroup

variable (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
  (c : Domain.FiniteCover d.obj)
  (hc : ∀ i, H ≤ ρ.locusOpenSubgroup (c.obj i))
  (Y : Action TopCat.{w} H)

/-- Equivariant maps on the actual cover components for any supplied open
subgroup preserving all components. -/
abbrev InvariantCoverFamily :=
  {g : ∀ i : Fin c.size,
      ρ.EquivariantLocusMap H ⟨c.obj i, hc i⟩ Y //
    c.Compatible (fun i => (g i).val)}

theorem invariantCoverEquivariant_iff (f : C(d.obj.locus, Y.V)) :
    ρ.LocusEquivariant H d Y f ↔
      ∀ i, ρ.LocusEquivariant H ⟨c.obj i, hc i⟩ Y (c.restrict f i) := by
  constructor
  · intro hf i g x
    exact hf g ((c.map i).locusMap x)
  · intro hf g x
    obtain ⟨i, hi⟩ := c.covers x.val x.property
    exact hf i g ⟨x.val, hi⟩

def invariantCoverRestrict (f : ρ.EquivariantLocusMap H d Y) :
    ρ.InvariantCoverFamily H d c hc Y :=
  ⟨fun i => ⟨c.restrict f.val i,
    (ρ.invariantCoverEquivariant_iff H d c hc Y f.val).mp f.property i⟩,
    c.compatible_restrict f.val⟩

/-- Use the original spectrum quotient lift and derive equivariance from the
component equations, at the prescribed subgroup. -/
def invariantCoverGlue (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.EquivariantLocusMap H d Y :=
  ⟨c.glue (fun i => (g.val i).val) g.property,
    (ρ.invariantCoverEquivariant_iff H d c hc Y _).mpr (by
      intro i
      exact Eq.mpr
        (congrArg (ρ.LocusEquivariant H ⟨c.obj i, hc i⟩ Y)
          (c.restrict_glue (fun i => (g.val i).val) g.property i))
        (g.val i).property)⟩

@[simp]
theorem invariantCoverRestrict_glue (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.invariantCoverRestrict H d c hc Y (ρ.invariantCoverGlue H d c hc Y g) = g := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact c.restrict_glue (fun i => (g.val i).val) g.property i

@[simp]
theorem invariantCoverGlue_restrict (f : ρ.EquivariantLocusMap H d Y) :
    ρ.invariantCoverGlue H d c hc Y (ρ.invariantCoverRestrict H d c hc Y f) = f := by
  apply Subtype.ext
  exact c.glue_restrict f.val

/-- Equivariant continuous gluing at any subgroup preserving the cover. -/
def invariantCoverGluingEquiv :
    ρ.EquivariantLocusMap H d Y ≃ ρ.InvariantCoverFamily H d c hc Y where
  toFun := ρ.invariantCoverRestrict H d c hc Y
  invFun := ρ.invariantCoverGlue H d c hc Y
  left_inv := ρ.invariantCoverGlue_restrict H d c hc Y
  right_inv := ρ.invariantCoverRestrict_glue H d c hc Y

/-- Restrict every component to a smaller subgroup, retaining compatibility. -/
def invariantCoverFamilySubgroup {J : OpenSubgroup G} (h : J ≤ H)
    (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.InvariantCoverFamily J ((ρ.invariantDomainRestriction h).obj d) c
      (fun i => h.trans (hc i))
      ((Action.res TopCat.{w} (openSubgroupInclusion h).toMonoidHom).obj Y) :=
  ⟨fun i => ρ.equivariantLocusMapRestriction h (g.val i), g.property⟩

theorem invariantCoverRestrict_subgroup {J : OpenSubgroup G} (h : J ≤ H)
    (f : ρ.EquivariantLocusMap H d Y) :
    ρ.invariantCoverFamilySubgroup H d c hc Y h
        (ρ.invariantCoverRestrict H d c hc Y f) =
      ρ.invariantCoverRestrict J ((ρ.invariantDomainRestriction h).obj d) c
        (fun i => h.trans (hc i))
        ((Action.res TopCat.{w} (openSubgroupInclusion h).toMonoidHom).obj Y)
        (ρ.equivariantLocusMapRestriction h f) :=
  rfl

/-- The actual continuous quotient lift commutes with subgroup restriction. -/
theorem invariantCoverGlue_subgroup {J : OpenSubgroup G} (h : J ≤ H)
    (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.equivariantLocusMapRestriction h (ρ.invariantCoverGlue H d c hc Y g) =
      ρ.invariantCoverGlue J ((ρ.invariantDomainRestriction h).obj d) c
        (fun i => h.trans (hc i))
        ((Action.res TopCat.{w} (openSubgroupInclusion h).toMonoidHom).obj Y)
        (ρ.invariantCoverFamilySubgroup H d c hc Y h g) :=
  rfl

variable {c} {hc}
  {b : Domain.FiniteCover d.obj}
  (hb : ∀ j, H ≤ ρ.locusOpenSubgroup (b.obj j))
  (r : Domain.FiniteCover.Refinement b c)

/-- Pull back through the actual selected bounded refinement arrows. -/
def invariantCoverRefinementPullback (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.InvariantCoverFamily H d b hb Y :=
  ⟨fun j => ⟨(g.val (r.index j)).val.comp (r.map j).locusMap,
    fun a x => (g.val (r.index j)).property a ((r.map j).locusMap x)⟩,
    r.compatible_pullbackFamily (fun i => (g.val i).val) g.property⟩

@[simp]
theorem invariantCoverRefinementPullback_apply
    (g : ρ.InvariantCoverFamily H d c hc Y)
    (j : Fin b.size) (x : (b.obj j).locus) :
    ((ρ.invariantCoverRefinementPullback H d Y hb r g).val j).val x =
      (g.val (r.index j)).val ((r.map j).locusMap x) :=
  rfl

/-- Refining global restrictions gives the original finer restrictions. -/
theorem invariantCoverRefinementPullback_restrict (f : ρ.EquivariantLocusMap H d Y) :
    ρ.invariantCoverRefinementPullback H d Y hb r
        (ρ.invariantCoverRestrict H d c hc Y f) =
      ρ.invariantCoverRestrict H d b hb Y f := by
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- Refinement preserves the exact equivariant continuous map obtained by gluing. -/
theorem invariantCoverGlue_refinement (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.invariantCoverGlue H d b hb Y
        (ρ.invariantCoverRefinementPullback H d Y hb r g) =
      ρ.invariantCoverGlue H d c hc Y g := by
  apply Subtype.ext
  exact r.glue_pullbackFamily (fun i => (g.val i).val) g.property

/-- Actual refinement restriction is an equivalence of equivariant compatible
families. Its inverse is finer gluing followed by coarser restriction. -/
def invariantCoverRefinementEquiv :
    ρ.InvariantCoverFamily H d c hc Y ≃ ρ.InvariantCoverFamily H d b hb Y where
  toFun := ρ.invariantCoverRefinementPullback H d Y hb r
  invFun g := ρ.invariantCoverRestrict H d c hc Y (ρ.invariantCoverGlue H d b hb Y g)
  left_inv g := by
    change ρ.invariantCoverRestrict H d c hc Y
      (ρ.invariantCoverGlue H d b hb Y
        (ρ.invariantCoverRefinementPullback H d Y hb r g)) = g
    rw [ρ.invariantCoverGlue_refinement H d Y hb r,
      ρ.invariantCoverRestrict_glue H d c hc Y]
  right_inv g := by
    rw [ρ.invariantCoverRefinementPullback_restrict H d Y hb r,
      ρ.invariantCoverRestrict_glue H d b hb Y]

/-- Different refinement choices induce the same restriction of compatible
equivariant families, without identifying their index choices. -/
theorem invariantCoverRefinementPullback_eq
    (s : Domain.FiniteCover.Refinement b c) (g : ρ.InvariantCoverFamily H d c hc Y) :
    ρ.invariantCoverRefinementPullback H d Y hb r g =
      ρ.invariantCoverRefinementPullback H d Y hb s g := by
  apply (ρ.invariantCoverGluingEquiv H d b hb Y).symm.injective
  exact (ρ.invariantCoverGlue_refinement H d Y hb r g).trans
    (ρ.invariantCoverGlue_refinement H d Y hb s g).symm

end FixedSubgroup

/-- At the original maximal common subgroup, the general construction is the
previous finite-cover equivariant gluing equivalence. -/
theorem invariantCoverGluingEquiv_finiteFamily (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (c : Domain.FiniteCover d.obj)
    (Y : Action TopCat.{w} (ρ.finiteFamilyOpenSubgroup H c.obj)) :
    ρ.invariantCoverGluingEquiv (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) c
        (ρ.finiteFamilyOpenSubgroup_le_stabilizer H c.obj) Y =
      ρ.finiteCoverGluingEquiv H d c Y :=
  rfl

section CommonSubgroup

variable (H : OpenSubgroup G) {V : Domain K P} (c b : Domain.FiniteCover V)

/-- Preserve both original covers by intersecting their common open stabilizers. -/
def commonCoverOpenSubgroup : OpenSubgroup G :=
  ρ.finiteFamilyOpenSubgroup H c.obj ⊓ ρ.finiteFamilyOpenSubgroup H b.obj

theorem commonCoverOpenSubgroup_le_left :
    ρ.commonCoverOpenSubgroup H c b ≤ ρ.finiteFamilyOpenSubgroup H c.obj :=
  inf_le_left

theorem commonCoverOpenSubgroup_le_right :
    ρ.commonCoverOpenSubgroup H c b ≤ ρ.finiteFamilyOpenSubgroup H b.obj :=
  inf_le_right

theorem commonCoverOpenSubgroup_le :
    ρ.commonCoverOpenSubgroup H c b ≤ H :=
  (ρ.commonCoverOpenSubgroup_le_left H c b).trans (ρ.finiteFamilyOpenSubgroup_le H c.obj)

@[simp]
theorem mem_commonCoverOpenSubgroup (g : G) :
    g ∈ ρ.commonCoverOpenSubgroup H c b ↔
      g ∈ H ∧ (∀ i, g ∈ ρ.locusOpenSubgroup (c.obj i)) ∧
        (∀ j, g ∈ ρ.locusOpenSubgroup (b.obj j)) := by
  simp only [commonCoverOpenSubgroup, OpenSubgroup.mem_inf,
    mem_finiteFamilyOpenSubgroup]
  tauto

theorem commonCoverOpenSubgroup_stabilizes_left (i : Fin c.size) :
    ρ.commonCoverOpenSubgroup H c b ≤ ρ.locusOpenSubgroup (c.obj i) :=
  (ρ.commonCoverOpenSubgroup_le_left H c b).trans
    (ρ.finiteFamilyOpenSubgroup_le_stabilizer H c.obj i)

theorem commonCoverOpenSubgroup_stabilizes_right (j : Fin b.size) :
    ρ.commonCoverOpenSubgroup H c b ≤ ρ.locusOpenSubgroup (b.obj j) :=
  (ρ.commonCoverOpenSubgroup_le_right H c b).trans
    (ρ.finiteFamilyOpenSubgroup_le_stabilizer H b.obj j)

end CommonSubgroup

/-- Every supplied actual refinement admits equivariant descent after explicitly
shrinking to the common open subgroup of its two unchanged covers. -/
def commonCoverRefinementEquiv (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    (c b : Domain.FiniteCover d.obj) (r : Domain.FiniteCover.Refinement b c)
    (Y : Action TopCat.{w} (ρ.commonCoverOpenSubgroup H c b)) :
    ρ.InvariantCoverFamily (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        c (ρ.commonCoverOpenSubgroup_stabilizes_left H c b) Y ≃
      ρ.InvariantCoverFamily (ρ.commonCoverOpenSubgroup H c b)
        ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
        b (ρ.commonCoverOpenSubgroup_stabilizes_right H c b) Y :=
  ρ.invariantCoverRefinementEquiv (ρ.commonCoverOpenSubgroup H c b)
    ((ρ.invariantDomainRestriction (ρ.commonCoverOpenSubgroup_le H c b)).obj d)
    Y (ρ.commonCoverOpenSubgroup_stabilizes_right H c b) r

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction
