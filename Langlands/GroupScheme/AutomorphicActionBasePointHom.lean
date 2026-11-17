import Langlands.GroupScheme.AutomorphicActionPointIso
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Adjoint.ActionFaithfulness
import Langlands.GroupScheme.Adjoint.RelativeQuotientIsomorphism

/-! # Base-point homomorphisms of automorphic actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {A G : GroupScheme S} (a : AutomorphicAction A G)

/-- Evaluating an automorphic action on sections is a group homomorphism
to the group of actual group-scheme automorphisms. -/
def basePointHom : (Over.mk (𝟙 S) ⟶ A.X) →* CategoryTheory.Aut G where
  toFun := a.basePointIso
  map_one' := by
    apply Aut.ext
    change (a.basePointIso 1).hom = 𝟙 G
    refine hom_ext_points fun T x => ?_
    rw [Grp.id_hom_hom, comp_basePointIso_hom, constantPoint_one,
      act_one_left, Category.comp_id]
  map_mul' x y := by
    apply Aut.ext
    change (a.basePointIso (x * y)).hom =
      (a.basePointIso y).hom ≫ (a.basePointIso x).hom
    refine hom_ext_points fun T g => ?_
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_basePointIso_hom,
      comp_basePointIso_hom, comp_basePointIso_hom, constantPoint_mul,
      act_mul_left]

@[simp]
theorem basePointHom_apply (x : Over.mk (𝟙 S) ⟶ A.X) :
    a.basePointHom x = a.basePointIso x := rfl

/-- A faithful action is injective on base-point automorphisms. -/
theorem basePointHom_injective (ha : a.IsFaithful) :
    Function.Injective a.basePointHom := by
  intro x y hxy
  apply ha x y
  intro W t g
  have h := congrArg (fun e : CategoryTheory.Aut G => g ≫ e.hom.hom.hom) hxy
  rw [basePointHom_apply, basePointHom_apply, comp_basePointIso_hom,
    comp_basePointIso_hom] at h
  have hx : A.constantPoint x W = t ≫ x := by
    unfold constantPoint
    congr 1
    exact Over.OverMorphism.ext t.w.symm
  have hy : A.constantPoint y W = t ≫ y := by
    unfold constantPoint
    congr 1
    exact Over.OverMorphism.ext t.w.symm
  rwa [hx, hy] at h

variable {a} {q : G ⟶ A}
  (hq : RelativeRoot.IsFppfQuotient (center G) q)
  (ha : a.restrict q = conjugation (𝟙 G))

include hq ha in
/-- The full-centre quotient acts injectively on the group scheme. -/
theorem basePointHom_injective_of_center_quotient :
    Function.Injective a.basePointHom :=
  a.basePointHom_injective (isFaithful_of_center_quotient q hq a ha)

include ha in
/-- The descended conjugation action on a point lifted through its quotient. -/
theorem act_center_quotient_lift {T : Over S} (x g : T ⟶ G.X) :
    a.act (x ≫ q.hom.hom) g = x * g * x⁻¹ := by
  rw [← restrict_act, ha, conjugation_act, Grp.id_hom_hom, Category.comp_id]

include ha in
/-- Every automorphism intertwines descended conjugation with its induced
automorphism of a supplied full-centre quotient. -/
theorem center_quotient_action_iso (e : G ≅ G) {T : Over S}
    (x : T ⟶ A.X) (g : T ⟶ G.X) :
    a.act x g ≫ e.hom.hom.hom =
      a.act (x ≫ (hq.mapIso hq e).hom.hom.hom) (g ≫ e.hom.hom.hom) := by
  let := hq.1
  let := hq.2.1
  apply hom_ext_of_flat_surjective_local_lift q x
  intro V b y hb
  have hsquare :
      (y ≫ q.hom.hom) ≫ (hq.mapIso hq e).hom.hom.hom =
        (y ≫ e.hom.hom.hom) ≫ q.hom.hom :=
    congrArg (fun f : G ⟶ A => y ≫ f.hom.hom) (hq.comp_mapIso_hom hq e)
  calc
    b ≫ (a.act x g ≫ e.hom.hom.hom) =
        a.act (b ≫ x) (b ≫ g) ≫ e.hom.hom.hom := by
      rw [← Category.assoc, a.naturality]
    _ = (y * (b ≫ g) * y⁻¹) ≫ e.hom.hom.hom := by
      rw [hb, act_center_quotient_lift ha]
    _ = (y ≫ e.hom.hom.hom) * ((b ≫ g) ≫ e.hom.hom.hom) *
        (y ≫ e.hom.hom.hom)⁻¹ := by
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    _ = a.act ((b ≫ x) ≫ (hq.mapIso hq e).hom.hom.hom)
        ((b ≫ g) ≫ e.hom.hom.hom) := by
      rw [hb, hsquare, act_center_quotient_lift ha]
    _ = b ≫ a.act (x ≫ (hq.mapIso hq e).hom.hom.hom)
        (g ≫ e.hom.hom.hom) := by
      rw [a.naturality, Category.assoc, Category.assoc]

include ha in
/-- The induced quotient automorphism transports the actual inner automorphism
of any base section. -/
theorem basePointIso_trans_center_quotient (e : G ≅ G)
    (x : Over.mk (𝟙 S) ⟶ A.X) :
    a.basePointIso x ≪≫ e =
      e ≪≫ a.basePointIso (x ≫ (hq.mapIso hq e).hom.hom.hom) := by
  apply Iso.ext
  refine hom_ext_points fun T g => ?_
  rw [Iso.trans_hom, Iso.trans_hom, Grp.comp_hom_hom, Grp.comp_hom_hom,
    ← Category.assoc, ← Category.assoc,
    comp_basePointIso_hom, comp_basePointIso_hom]
  have hx :
      A.constantPoint (x ≫ (hq.mapIso hq e).hom.hom.hom) T =
        A.constantPoint x T ≫ (hq.mapIso hq e).hom.hom.hom :=
    (Category.assoc _ _ _).symm
  rw [hx]
  exact center_quotient_action_iso hq ha e _ g

include hq ha in
/-- Inner automorphisms coming from a supplied full-centre fppf quotient
form a normal subgroup over any scheme base. -/
theorem basePointHom_range_normal_of_center_quotient :
    a.basePointHom.range.Normal := by
  refine ⟨?_⟩
  rintro n ⟨x, rfl⟩ e
  refine ⟨x ≫ (hq.mapIso hq e).hom.hom.hom, ?_⟩
  have he :
      e * a.basePointHom x =
        a.basePointHom (x ≫ (hq.mapIso hq e).hom.hom.hom) * e :=
    basePointIso_trans_center_quotient hq ha e x
  exact (mul_inv_eq_iff_eq_mul.mpr he).symm

end Langlands.GroupScheme.AutomorphicAction
