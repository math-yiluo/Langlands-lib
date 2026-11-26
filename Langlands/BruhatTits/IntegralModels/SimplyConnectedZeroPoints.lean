import Langlands.Geometry.Building.UnramifiedSimplyConnectedZero
import Langlands.Geometry.Building.UnramifiedZeroTransport
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # `G(K)^1 = G(K)^0 = G(K)` for a simply connected group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.BruhatTits.IntegralModels

open Langlands.Geometry.Building

section Field

variable {k : Type u} [Field k]

/-- A semisimple group has no nontrivial rational character: the identity exhibits the
derived subgroup, because a semisimple group is perfect, and every rational character
vanishes on the derived subgroup. -/
theorem rationalCharacters_subsingleton_of_isSemisimple
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) :
    Subsingleton (rationalCharacters G) := by
  have hderived : IsDerivedSubgroup (𝟙 G) := by
    refine ⟨IsClosedSubgroup.of_iso (Iso.refl G), ?_⟩
    rw [semisimplePerfect k G hG]
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    simp only [SubgroupFunctor.top_carrier, Subgroup.mem_top, iff_true]
    exact SubgroupFunctor.mem_range.2 ⟨x, by simp⟩
  constructor
  intro χ ψ
  have hχ := hderived.characterRestrict_eq_zero χ
  have hψ := hderived.characterRestrict_eq_zero ψ
  rw [characterRestrict_id] at hχ hψ
  exact hχ.trans hψ.symm

/-- For a semisimple group the common kernel of the valuations of the rational characters is
the whole group of rational points. -/
theorem characterValuationKernel_eq_top_of_isSemisimple {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation k Γ₀)
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSemisimple G) :
    characterValuationKernel v G = ⊤ := by
  have := rationalCharacters_subsingleton_of_isSemisimple hG
  rw [eq_top_iff]
  intro g _
  rw [mem_characterValuationKernel]
  intro χ
  rw [Subsingleton.elim χ 0, rationalCharacterEval_zero, Units.val_one, map_one]

/-- A closed subgroup whose range is every point is an isomorphism. -/
private theorem isIso_of_isClosedSubgroup_of_range_eq_top
    {G P : GroupScheme (Spec (CommRingCat.of k))} (p : P ⟶ G)
    (hp : IsClosedSubgroup p) (h : SubgroupFunctor.range p = ⊤) : IsIso p := by
  let : IsClosedImmersion p.hom.hom.left := hp
  have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, h⟩
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro Q
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨x, Category.comp_id x⟩
  let e := hrep.isoOfIsRepresentedBy hid
  have he : e.hom = p := by
    simpa using hrep.isoOfIsRepresentedBy_hom_comp hid
  rw [← he]
  infer_instance

/-- If `G` is simply connected, the map `π ≫ d : C → G` of a simply connected derived cover
is an isomorphism: `d` is an isomorphism because `G` is perfect, and then `π ≫ d` is a
central isogeny from a semisimple group onto the simply connected group `G`. -/
theorem IsSimplyConnectedDerivedCover.isIso_comp_of_isSimplyConnected
    {G D C : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) (hG : IsSimplyConnected G) : IsIso (π ≫ d) := by
  have hrange : SubgroupFunctor.range d = ⊤ := by
    rw [h.isDerivedSubgroup.2]
    exact semisimplePerfect k G hG.isSemisimple
  have : IsIso d := isIso_of_isClosedSubgroup_of_range_eq_top d h.isDerivedSubgroup.1 hrange
  have hc : IsCentralIsogeny (π ≫ d) :=
    h.isSimplyConnectedCover.isCentralIsogeny.comp_iso (asIso d)
  exact hG.central_isogeny_isIso C (π ≫ d)
    h.isSimplyConnectedCover.isSimplyConnected.isSemisimple hc

/-- If `G` is simply connected, the image of `G_sc(k) → G(k)` is all of `G(k)`. -/
theorem simplyConnectedImage_eq_top_of_isSimplyConnected
    {G D C : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) (hG : IsSimplyConnected G) :
    simplyConnectedImage d π = ⊤ := by
  have := IsSimplyConnectedDerivedCover.isIso_comp_of_isSimplyConnected h hG
  rw [eq_top_iff]
  intro g _
  refine mem_simplyConnectedImage.2 ⟨rationalPoints.map (inv (π ≫ d)) g, ?_⟩
  rw [← rationalPoints.map_comp_apply, IsIso.inv_hom_id]
  simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]

end Field

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **KP Definition 2.6.23(1) for a simply connected group.** If `H` over the maximal
unramified extension is simply connected, then `H(K)^0 = H(K)`, whichever datum computes it. -/
theorem UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected
    {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}
    (E : UnramifiedZeroDatum F H) (hH : IsSimplyConnected H) : E.zeroPoints = ⊤ :=
  Langlands.Geometry.Building.UnramifiedZeroDatum.zeroPoints_eq_top_of_isSimplyConnected E hH

end Local

end Langlands.BruhatTits.IntegralModels
