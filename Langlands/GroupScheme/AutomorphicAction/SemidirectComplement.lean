import Langlands.GroupScheme.AutomorphicAction.SemidirectTorus
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Restricting an external semidirect complement to the original group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section General

variable {B : Scheme.{u}} {S G U : GroupScheme B} (a : AutomorphicAction S G)
    (u : U ⟶ a.semidirectProduct) (i : U ⟶ G)
    (hi : i ≫ a.semidirectInl = u)

include hi

/-- Membership in a factor inside the normal coordinate can be checked in
the external semidirect product, on every test scheme. -/
theorem mem_range_semidirectNormalFactor_iff {V : Over B} (g : V ⟶ G.X) :
    g ∈ (SubgroupFunctor.range i).carrier V ↔
      g ≫ a.semidirectInl.hom.hom ∈ (SubgroupFunctor.range u).carrier V := by
  change (∃ x : V ⟶ U.X, x ≫ i.hom.hom = g) ↔
    ∃ x : V ⟶ U.X, x ≫ u.hom.hom = g ≫ a.semidirectInl.hom.hom
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hi]
  · rintro ⟨x, hx⟩
    refine ⟨x, (cancel_mono a.semidirectInl.hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hi]
    exact hx

/-- Normality in the external product gives normality in the original
normal factor. -/
theorem semidirectNormalFactor_isNormal
    (hu : (SubgroupFunctor.range u).IsNormal) :
    (SubgroupFunctor.range i).IsNormal := by
  intro V g x _ hx
  apply (a.mem_range_semidirectNormalFactor_iff u i hi _).mpr
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  exact hu V _ _ (Subgroup.mem_top _)
    ((a.mem_range_semidirectNormalFactor_iff u i hi x).mp hx)

/-- Normality in the external product also gives stability under the
original external action, with no restriction on the test scheme. -/
theorem semidirectNormalFactor_isStable
    (hu : (SubgroupFunctor.range u).IsNormal) :
    a.IsStable (SubgroupFunctor.range i) := by
  intro V s g hg
  apply (a.mem_range_semidirectNormalFactor_iff u i hi _).mpr
  rw [← a.semidirect_conjugation, conjugation_act]
  exact hu V _ _ (Subgroup.mem_top _)
    ((a.mem_range_semidirectNormalFactor_iff u i hi g).mp hg)

variable {M : CommGroupScheme B} (j : M.toGrp ⟶ a.semidirectProduct)

/-- An actual multiplication decomposition of the external product restricts
to a multiplication decomposition of its normal coordinate and the actual
scheme-theoretic intersection with the commutative factor. -/
theorem isIso_subgroupMultiplication_semidirectIntersection
    [IsIso (subgroupMultiplication u j)] :
    IsIso (subgroupMultiplication i (a.semidirectTorusIntersectionInclusion j)) := by
  let p := a.semidirectTorusIntersectionFst j
  let t := a.semidirectTorusIntersectionInclusion j
  let hpb := subgroupIntersection_isPullback j a.semidirectInl
  have hpmono : Mono p.hom.hom := hpb.mono_fst_of_mono
  let := hpmono
  have hpoint {V : Over B}
      (w : V ⟶ U.X ⊗ (a.semidirectTorusIntersection j).X) :
      (w ≫ subgroupMultiplication i t) ≫ a.semidirectInl.hom.hom =
        lift (w ≫ fst _ _) (w ≫ snd _ _ ≫ p.hom.hom) ≫
          subgroupMultiplication u j := by
    rw [comp_subgroupMultiplication_eq, MonObj.mul_comp,
      comp_subgroupMultiplication_eq, lift_fst_assoc, lift_snd_assoc]
    have hit := congrArg (fun f => f.hom.hom) hi
    have htp := congrArg (fun f => f.hom.hom)
      (a.semidirectTorusIntersection_condition j)
    change p.hom.hom ≫ j.hom.hom = t.hom.hom ≫ a.semidirectInl.hom.hom at htp
    change i.hom.hom ≫ a.semidirectInl.hom.hom = u.hom.hom at hit
    simp only [Category.assoc]
    rw [hit, ← htp]
  refine isIso_of_yoneda_map_bijective _ fun V => ⟨fun w w' he => ?_, fun g => ?_⟩
  · change w ≫ subgroupMultiplication i t = w' ≫ subgroupMultiplication i t at he
    have ha :
        lift (w ≫ fst _ _) (w ≫ snd _ _ ≫ p.hom.hom) =
          lift (w' ≫ fst _ _) (w' ≫ snd _ _ ≫ p.hom.hom) := by
      apply (cancel_mono (subgroupMultiplication u j)).mp
      rw [← hpoint, ← hpoint, he]
    have hleft := congrArg (· ≫ fst U.X M.X) ha
    have hright := congrArg (· ≫ snd U.X M.X) ha
    simp only [lift_fst, lift_snd] at hleft hright
    apply CartesianMonoidalCategory.hom_ext
    · exact hleft
    · exact (cancel_mono p.hom.hom).mp hright
  · let w := (g ≫ a.semidirectInl.hom.hom) ≫ inv (subgroupMultiplication u j)
    let x := w ≫ fst U.X M.X
    let y := w ≫ snd U.X M.X
    have hw : w ≫ subgroupMultiplication u j = g ≫ a.semidirectInl.hom.hom := by
      simp only [w, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hmul : (x ≫ u.hom.hom) * (y ≫ j.hom.hom) =
        g ≫ a.semidirectInl.hom.hom := by
      simpa only [x, y, comp_subgroupMultiplication_eq, Category.assoc] using hw
    have hy : y ≫ j.hom.hom ∈ (SubgroupFunctor.range a.semidirectInl).carrier V := by
      have he : y ≫ j.hom.hom =
          (x ≫ u.hom.hom)⁻¹ * (g ≫ a.semidirectInl.hom.hom) := by
        rw [← hmul, inv_mul_cancel_left]
      rw [he]
      apply Subgroup.mul_mem
      · apply Subgroup.inv_mem
        refine ⟨x ≫ i.hom.hom, ?_⟩
        change (x ≫ i.hom.hom) ≫ a.semidirectInl.hom.hom = x ≫ u.hom.hom
        rw [Category.assoc, ← Grp.comp_hom_hom, hi]
      · exact ⟨g, rfl⟩
    change ∃ z : V ⟶ G.X, z ≫ a.semidirectInl.hom.hom = y ≫ j.hom.hom at hy
    obtain ⟨z, hz⟩ := hy
    let v := hpb.lift y z hz.symm
    refine ⟨lift x v, (cancel_mono a.semidirectInl.hom.hom).mp ?_⟩
    rw [hpoint, lift_fst, lift_snd_assoc]
    have hv : v ≫ p.hom.hom = y := hpb.lift_fst _ _ _
    rw [hv]
    change lift (w ≫ fst U.X M.X) (w ≫ snd U.X M.X) ≫
      subgroupMultiplication u j = g ≫ a.semidirectInl.hom.hom
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
    exact hw

end General

section Field

variable {k : Type u} [Field k]
    {S G U : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction S G) (u : U ⟶ a.semidirectProduct)
    (hU : IsUnipotent U) (hS : IsSplitTorus S)

include hU hS in
/-- A unipotent subgroup of the external semidirect product lies in its
normal coordinate because its projection to the split torus is trivial on
every scheme test. -/
theorem range_le_semidirectInl_of_isUnipotent :
    SubgroupFunctor.range u ≤ SubgroupFunctor.range a.semidirectInl := by
  intro V x hx
  change ∃ y : V ⟶ U.X, y ≫ u.hom.hom = x at hx
  obtain ⟨y, rfl⟩ := hx
  rw [a.mem_range_semidirectInl_iff, Category.assoc]
  exact hU.comp_eq_one_of_isSplitTorus hS (u ≫ a.semidirectProjection) V y

variable [Mono u.hom.hom]

/-- The actual inclusion of an external unipotent subgroup in the original
normal coordinate. -/
def semidirectNormalSubgroup : U ⟶ G :=
  SubgroupFunctor.factorOfRangeLE (a.range_le_semidirectInl_of_isUnipotent u hU hS)

/-- The constructed inclusion recovers the supplied external subgroup. -/
theorem semidirectNormalSubgroup_comp :
    a.semidirectNormalSubgroup u hU hS ≫ a.semidirectInl = u :=
  SubgroupFunctor.factorOfRangeLE_comp _

end Field

end Langlands.GroupScheme.AutomorphicAction
