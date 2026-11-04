import Langlands.GroupScheme.AutomorphicAction.SemidirectDynamic
import Langlands.GroupScheme.Dynamic.UnipotentCentralizerRestriction
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Actual unipotent intersections in a semidirect ambient group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.AutomorphicAction

section CentralCocharacter

variable {S : Scheme.{u}} {H N : GroupScheme S}
  (a : AutomorphicAction H N) (chi : (Gm S).toGrp ⟶ H)
  (hcentral : Dynamic.centralizer chi = ⊤)

include hcentral

/-- Only centrality of the chosen cocharacter is needed for invariance of
projection; the entire acting factor need not be commutative. -/
theorem semidirectProjection_isInvariant_of_central :
    (cocharacterAction (chi ≫ a.semidirectInr)).IsInvariantMorphism
      a.semidirectProjection.hom.hom := by
  intro T t x
  rw [cocharacterAction_act, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have ht : (t ≫ (chi ≫ a.semidirectInr).hom.hom) ≫
      a.semidirectProjection.hom.hom = t ≫ chi.hom.hom := by
    rw [Grp.comp_hom_hom, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, semidirectInr_comp_projection, Grp.id_hom_hom,
      Category.comp_id]
  rw [ht]
  have hx : x ≫ a.semidirectProjection.hom.hom ∈ (Dynamic.centralizer chi).carrier T := by
    rw [hcentral]
    exact Subgroup.mem_top _
  rw [← (Dynamic.commute_cocharacter_of_mem_centralizer chi hx t).eq,
    mul_inv_cancel_right]

/-- All identity-limit points lie in the normal factor when the chosen
cocharacter is central in the separated acting group. -/
theorem semidirect_unipotent_le_range_of_central [IsSeparated H.X.hom] :
    Dynamic.unipotent (chi ≫ a.semidirectInr) ≤ SubgroupFunctor.range a.semidirectInl := by
  rw [a.range_semidirectInl]
  have h := (cocharacterAction (chi ≫ a.semidirectInr)).unipotent_le_comap_bot_of_invariant
    a.semidirectProjection (a.semidirectProjection_isInvariant_of_central chi hcentral)
  rwa [cocharacterAction_unipotent] at h

/-- The normal-factor identity-limit functor gives the entire ambient one. -/
theorem semidirect_unipotent_map_of_central [IsSeparated H.X.hom] :
    (a.restrict chi).unipotent.map a.semidirectInl =
      Dynamic.unipotent (chi ≫ a.semidirectInr) := by
  have h := IsEquivariant.range_inf_unipotent (a.semidirectInl_isEquivariant chi)
    a.isClosedSubgroup_semidirectInl
  rw [cocharacterAction_unipotent] at h
  have hle : SubgroupFunctor.range a.semidirectInl ⊓
      Dynamic.unipotent (chi ≫ a.semidirectInr) =
      Dynamic.unipotent (chi ≫ a.semidirectInr) :=
    SubgroupFunctor.ext fun T =>
      inf_eq_right.mpr (a.semidirect_unipotent_le_range_of_central chi hcentral T)
  rw [hle] at h
  exact h.symm

/-- Any representative of the original identity-limit functor becomes a
representative of the full ambient dynamic unipotent functor. -/
theorem isRepresentedBy_semidirectInl_comp_of_central [IsSeparated H.X.hom]
    {U : GroupScheme S} {j : U ⟶ N} (hj : (a.restrict chi).unipotent.IsRepresentedBy j) :
    (Dynamic.unipotent (chi ≫ a.semidirectInr)).IsRepresentedBy (j ≫ a.semidirectInl) := by
  have : Mono j.hom.hom := hj.1
  refine ⟨by rw [Grp.comp_hom_hom]; infer_instance, ?_⟩
  rw [← a.semidirect_unipotent_map_of_central chi hcentral, ← hj.2]
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y ≫ j.hom.hom, ⟨y, rfl⟩, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨n, hn, hn'⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hn
    refine ⟨y, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc, hy]
    exact hn'

/-- Every point of the acting factor centralizes the lifted cocharacter. -/
theorem range_semidirectInr_le_centralizer_of_central :
    SubgroupFunctor.range a.semidirectInr ≤ Dynamic.centralizer (chi ≫ a.semidirectInr) := by
  intro T x hx
  obtain ⟨h, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hh : h ∈ (Dynamic.centralizer chi).carrier T := by
    rw [hcentral]
    exact Subgroup.mem_top _
  exact Dynamic.centralizer_le_comap chi a.semidirectInr T hh

/-- Every homomorphism through the acting factor still centralizes the lifted
central cocharacter. -/
theorem range_comp_semidirectInr_le_centralizer_of_central
    {Z : GroupScheme S} (fZ : Z ⟶ H) :
    SubgroupFunctor.range (fZ ≫ a.semidirectInr) ≤
      Dynamic.centralizer (chi ≫ a.semidirectInr) := by
  intro T z hz
  obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  apply a.range_semidirectInr_le_centralizer_of_central chi hcentral T
  exact SubgroupFunctor.mem_range.mpr ⟨z ≫ fZ.hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

end CentralCocharacter

end Langlands.GroupScheme.AutomorphicAction

namespace Langlands.GroupScheme.Dynamic

section Intersection

variable {S : Scheme.{u}} {G H N U Z : GroupScheme S}
  (chi psi : (Gm S).toGrp ⟶ G) (iH : H ⟶ G) {iN : N ⟶ G} {iU : U ⟶ G}
  (hH : SubgroupFunctor.range iH ≤ centralizer chi)
  (hH' : SubgroupFunctor.range iH ≤ centralizer psi)
  (hHc : IsClosedSubgroup iH)
  (hN : (unipotent psi).IsRepresentedBy iN) (hNc : IsClosedSubgroup iN)
  (chiH : (Gm S).toGrp ⟶ H) (hchi : chiH ≫ iH = chi)
  (hU : (unipotent chi ⊓ unipotent psi).IsRepresentedBy iU)
  (fU : U ⟶ N) (hfU : fU ≫ iN = iU)

include hH hHc hchi in
/-- The lifted cocharacter is central in any monic subgroup contained in its
ambient centralizer. -/
theorem centralizer_factor_eq_top : centralizer chiH = ⊤ := by
  rw [centralizer_eq_comap_of_isClosedSubgroup chiH iH hHc, hchi]
  exact SubgroupFunctor.range_le_iff_comap_eq_top.mp hH

include hH' hN hchi in
/-- The normal-factor inclusion intertwines the induced cocharacter action
with the original ambient conjugation. -/
theorem centralizingUnipotentAction_restrict_isEquivariant :
    ((centralizingUnipotentAction psi iH hH' hN).restrict chiH).IsEquivariant
      (AutomorphicAction.cocharacterAction chi) iN := by
  intro T t n
  rw [AutomorphicAction.restrict_act, centralizingUnipotentAction_act_comp,
    AutomorphicAction.cocharacterAction_act, Category.assoc, ← Grp.comp_hom_hom, hchi]

include hH' hN hNc hchi hU hfU in
/-- The displayed positive/positive representative is the identity-limit
subgroup for the actual action on the second unipotent group. -/
theorem isRepresentedBy_unipotentIntersection_factor :
    ((centralizingUnipotentAction psi iH hH' hN).restrict chiH).unipotent.IsRepresentedBy fU := by
  have : IsClosedImmersion iN.hom.hom.left := hNc
  have : Mono iN.hom.hom := hN.1
  have : Mono iU.hom.hom := hU.1
  have hfac : fU.hom.hom ≫ iN.hom.hom = iU.hom.hom := by
    rw [← Grp.comp_hom_hom, hfU]
  refine ⟨mono_of_mono_fac hfac, ?_⟩
  have hrange : SubgroupFunctor.range (fU ≫ iN) =
      SubgroupFunctor.range iN ⊓ unipotent chi := by
    rw [hfU, hU.2, hN.2]
    apply SubgroupFunctor.ext
    intro T
    exact inf_comm _ _
  have hr := SubgroupFunctor.range_eq_comap_of_range_comp_eq_inf
    fU iN (unipotent chi) hrange
  have hequiv :
      ((centralizingUnipotentAction psi iH hH' hN).restrict chiH).IsEquivariant
        (AutomorphicAction.cocharacterAction chi) iN :=
    centralizingUnipotentAction_restrict_isEquivariant chi psi iH hH' hN chiH hchi
  have heq := AutomorphicAction.IsEquivariant.unipotent_eq_comap_of_isClosedSubgroup
    hequiv hNc
  rw [AutomorphicAction.cocharacterAction_unipotent] at heq
  exact hr.trans heq.symm

include hH hH' hHc hN hNc hchi hU hfU in
/-- The same U represents a dynamic unipotent subgroup in the semidirect
ambient group used for Haar comparison. -/
theorem isRepresentedBy_unipotentIntersection_semidirect [IsSeparated H.X.hom] :
    (unipotent (chiH ≫ (centralizingUnipotentAction psi iH hH' hN).semidirectInr)).IsRepresentedBy
      (fU ≫ (centralizingUnipotentAction psi iH hH' hN).semidirectInl) :=
  AutomorphicAction.isRepresentedBy_semidirectInl_comp_of_central _ chiH
    (centralizer_factor_eq_top chi iH hH hHc chiH hchi)
    (isRepresentedBy_unipotentIntersection_factor chi psi iH hH' hN hNc chiH hchi hU fU hfU)

variable [IsSeparated H.X.hom] (fZ : Z ⟶ H)

/-- Actual conjugation on U computed in the semidirect ambient group. -/
def semidirectUnipotentIntersectionAction : AutomorphicAction Z U :=
  centralizingUnipotentAction
    (chiH ≫ (centralizingUnipotentAction psi iH hH' hN).semidirectInr)
    (fZ ≫ (centralizingUnipotentAction psi iH hH' hN).semidirectInr)
    (AutomorphicAction.range_comp_semidirectInr_le_centralizer_of_central
      (centralizingUnipotentAction psi iH hH' hN) chiH
      (centralizer_factor_eq_top chi iH hH hHc chiH hchi) fZ)
    (isRepresentedBy_unipotentIntersection_semidirect
      chi psi iH hH hH' hHc hN hNc chiH hchi hU fU hfU)

variable (iZ : Z ⟶ G)
  (hZ : SubgroupFunctor.range iZ ≤ centralizer chi)
  (hZ' : SubgroupFunctor.range iZ ≤ centralizer psi)
  (hfZ : fZ ≫ iH = iZ)

include hH hH' hHc hN hNc hchi hU hfU hfZ in
/-- The semidirect action equals the original ambient intersection action
on the same U, with the original forward conjugation convention. -/
theorem semidirectUnipotentIntersectionAction_eq :
    semidirectUnipotentIntersectionAction
        chi psi iH hH hH' hHc hN hNc chiH hchi hU fU hfU fZ =
      centralizingUnipotentIntersectionAction chi psi iZ hZ hZ' hU := by
  let a := centralizingUnipotentAction psi iH hH' hN
  let b := semidirectUnipotentIntersectionAction
    chi psi iH hH hH' hHc hN hNc chiH hchi hU fU hfU fZ
  have : Mono iU.hom.hom := hU.1
  apply AutomorphicAction.ext_act
  intro T z x
  have hb : b.act z x ≫ fU.hom.hom =
      a.act (z ≫ fZ.hom.hom) (x ≫ fU.hom.hom) := by
    apply (cancel_mono a.semidirectInl.hom.hom).mp
    rw [Category.assoc]
    change b.act z x ≫ (fU ≫ a.semidirectInl).hom.hom = _
    dsimp only [b, semidirectUnipotentIntersectionAction]
    rw [centralizingUnipotentAction_act_comp]
    rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc]
    simpa only [AutomorphicAction.conjugation_act] using
      a.semidirect_conjugation (z ≫ fZ.hom.hom) (x ≫ fU.hom.hom)
  apply (cancel_mono iU.hom.hom).mp
  calc
    _ = (b.act z x ≫ fU.hom.hom) ≫ iN.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hfU]
    _ = (z ≫ iZ.hom.hom) * (x ≫ iU.hom.hom) * (z ≫ iZ.hom.hom)⁻¹ := by
      rw [hb, centralizingUnipotentAction_act_comp,
        Category.assoc, ← Grp.comp_hom_hom, hfZ,
        Category.assoc, ← Grp.comp_hom_hom, hfU]
    _ = _ := (centralizingUnipotentIntersectionAction_act_comp
      chi psi iZ hZ hZ' hU z x).symm

end Intersection

end Langlands.GroupScheme.Dynamic
