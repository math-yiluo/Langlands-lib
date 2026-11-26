import Langlands.GroupScheme.Unipotent.PowerBijectiveStatement
import Langlands.GroupScheme.Absolute.SmoothRationalPointClosure
import Langlands.GroupScheme.Commutative.CharZeroUnipotentVectorProof
import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Rational.RootHeisenbergChartPoints
import Langlands.GroupScheme.Rational.UnipotentPointsPGroup
import Langlands.GroupScheme.SubgroupIntersection

/-! # Prime-to-the-characteristic powers on unipotent points -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private theorem bijective_zpow_of_vectorGroup {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} (hV : RelativeRoot.IsVectorGroup V)
    {e : ℤ} (he : (e : k) ≠ 0) : Function.Bijective (fun x : rationalPoints V => x ^ e) := by
  obtain ⟨d, coordinates, _⟩ := hV
  let E := RelativeRoot.rationalVectorCoordinates coordinates
  have hcoord (x : rationalPoints V) (i : Fin d) :
      (E (x ^ e)).toAdd i = (e : k) * (E x).toAdd i := by
    rw [map_zpow]
    change e • (E x).toAdd i = _
    exact zsmul_eq_mul _ _
  constructor
  · intro x y h
    change x ^ e = y ^ e at h
    apply E.injective
    apply Multiplicative.toAdd.injective
    funext i
    apply mul_left_cancel₀ he
    rw [← hcoord, ← hcoord, h]
  · intro x
    refine ⟨E.symm (Multiplicative.ofAdd (fun i => (e : k)⁻¹ * (E x).toAdd i)), ?_⟩
    apply E.injective
    apply Multiplicative.toAdd.injective
    funext i
    rw [hcoord, MulEquiv.apply_symm_apply, toAdd_ofAdd, ← mul_assoc,
      mul_inv_cancel₀ he, one_mul]

section CharZero

variable {k : Type u} [Field k] [CharZero k]
    {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom U.X.hom] [LocallyOfFiniteType U.X.hom] {e : ℤ}

private theorem bijective_zpow_on_pointEnvelope (hU : IsUnipotent U) (he : (e : k) ≠ 0)
    {x : rationalPoints U}
    (C : SmoothCommutativePointEnvelope U x) :
    Function.Bijective (fun y : rationalPoints C.group.toGrp => y ^ e) := by
  have : IsClosedImmersion C.inclusion.hom.hom.left := C.closed
  have : IsAffineHom C.group.toGrp.X.hom := C.affine
  have : LocallyOfFiniteType C.group.toGrp.X.hom := by
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  exact bijective_zpow_of_vectorGroup
    (charZeroCommutativeUnipotentVectorGroup k C.group.toGrp
      (unipotentClosedSubgroup k U _ C.inclusion C.closed hU)) he

private theorem surjective_rationalPoints_zpow_charZero (hU : IsUnipotent U) (he : (e : k) ≠ 0) :
    Function.Surjective (fun x : rationalPoints U => x ^ e) := by
  intro x
  let C := smoothCommutativePointEnvelope U x
  obtain ⟨r, hr⟩ := (bijective_zpow_on_pointEnvelope hU he C).surjective C.point
  exact ⟨rationalPoints.map C.inclusion r,
    ((map_zpow (rationalPoints.map C.inclusion) r e).symm.trans
      (congrArg (rationalPoints.map C.inclusion) hr)).trans C.point_inclusion⟩

private theorem bijective_rationalPoints_zpow_charZero (hU : IsUnipotent U) (he : (e : k) ≠ 0) :
    Function.Bijective (fun x : rationalPoints U => x ^ e) := by
  refine ⟨?_, surjective_rationalPoints_zpow_charZero hU he⟩
  have eq_one_of_zpow_eq_one (t : rationalPoints U) (ht : t ^ e = 1) : t = 1 := by
    let C := smoothCommutativePointEnvelope U t
    have : IsClosedImmersion C.inclusion.hom.hom.left := C.closed
    have : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
    have h : C.point ^ e = (1 : rationalPoints C.group.toGrp) ^ e := by
      apply (cancel_mono C.inclusion.hom.hom).mp
      change rationalPoints.map C.inclusion (C.point ^ e) = rationalPoints.map C.inclusion (1 ^ e)
      rw [map_zpow, C.point_inclusion, ht, one_zpow, map_one]
    rw [← C.point_inclusion, (bijective_zpow_on_pointEnvelope hU he C).injective h, map_one]
  intro x y hxy
  change x ^ e = y ^ e at hxy
  -- Extract a root of the common power in a subgroup that commutes with both points.
  obtain ⟨Cx, ix, hix, hcx⟩ := U.pointCentralizer_isClosedRepresentable x
  obtain ⟨Cy, iy, hiy, hcy⟩ := U.pointCentralizer_isClosedRepresentable y
  let C := subgroupIntersection ix iy
  let j : C ⟶ U := subgroupIntersectionHom ix iy
  have hj := isClosedSubgroup_subgroupIntersectionHom hcx hcy
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have hC : IsUnipotent C := unipotentClosedSubgroup k U C j hj hU
  let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  have hmem (w : rationalPoints U) :
      w ∈ (SubgroupFunctor.range j).carrier T ↔ Commute w x ∧ Commute w y := by
    change w ∈ (SubgroupFunctor.range (subgroupIntersectionHom ix iy)).carrier T ↔ _
    rw [range_subgroupIntersectionHom, hix.2, hiy.2]
    change (w ∈ (U.pointCentralizer x).carrier T ∧ w ∈ (U.pointCentralizer y).carrier T) ↔ _
    have hT : toUnit T = 𝟙 T := toUnit_unique _ _
    rw [U.mem_pointCentralizer, U.mem_pointCentralizer, hT, Category.id_comp, Category.id_comp]
    rfl
  have hp : x ^ e ∈ (SubgroupFunctor.range j).carrier T :=
    (hmem (x ^ e)).2 ⟨Commute.zpow_self x e, hxy.symm ▸ Commute.zpow_self y e⟩
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hp
  obtain ⟨rC, hrC⟩ := surjective_rationalPoints_zpow_charZero hC he w
  change rC ^ e = w at hrC
  let r := rationalPoints.map j rC
  have hr : r ^ e = x ^ e := by
    change (rationalPoints.map j rC) ^ e = x ^ e
    rw [← map_zpow, hrC]
    exact hw
  have hc := (hmem r).1 (SubgroupFunctor.mem_range.mpr ⟨rC, rfl⟩)
  have eq_root (a : rationalPoints U) (ha : a ^ e = r ^ e) (hcomm : Commute a r) : a = r := by
    apply div_eq_one.mp
    apply eq_one_of_zpow_eq_one
    rw [div_eq_mul_inv, hcomm.inv_right.mul_zpow, inv_zpow, ha, mul_inv_cancel]
  exact (eq_root x hr.symm hc.1.symm).trans (eq_root y (hxy.symm.trans hr.symm) hc.2.symm).symm

end CharZero

/-- On geometric points of an affine unipotent group of finite type, the integer power map
is bijective if the exponent has nonzero image in the base field. -/
theorem unipotentPowerBijective : UnipotentPowerBijectiveStatement.{u} := by
  intro k _ U _ _ hU e he
  rcases CharP.exists' k with hzero | ⟨p, hp, hchar⟩
  · let := hzero
    let K := AlgebraicClosure k
    let b := toAlgebraicClosure k
    let V := (GroupScheme.baseChange b).obj U
    have : IsAffineHom V.X.hom := by
      change IsAffineHom (Limits.pullback.snd U.X.hom b)
      infer_instance
    have : LocallyOfFiniteType V.X.hom := by
      change LocallyOfFiniteType (Limits.pullback.snd U.X.hom b)
      infer_instance
    have heK : (e : K) ≠ 0 := by
      intro hz
      apply he
      apply (algebraMap k K).injective
      rw [map_intCast, map_zero, hz]
    let E := baseChangeBasePointsEquiv b U
    have hV := bijective_rationalPoints_zpow_charZero (U := V) hU.baseChange heK
    have hconj : E ∘ (fun x : rationalPoints V => x ^ e) ∘ E.symm =
        (fun x : Over.mk b ⟶ U.X => x ^ e) := by
      funext x
      change E ((E.symm x) ^ e) = x ^ e
      rw [map_zpow, E.apply_symm_apply]
    change Function.Bijective (fun x : Over.mk b ⟶ U.X => x ^ e)
    rw [← hconj]
    exact E.bijective.comp (hV.comp E.symm.bijective)
  · let := hp
    let := hchar
    let T := Over.mk (toAlgebraicClosure k)
    have hndvd : ¬ p ∣ e.natAbs := by
      intro hd
      exact he ((CharP.intCast_eq_zero_iff k p e).2
        (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hd)))
    have hpow : Function.Bijective (fun x : T ⟶ U.X => x ^ e.natAbs) :=
      ((isPGroup_testPoints_of_isUnipotent p hU T).powEquiv' hndvd).bijective
    cases e with
    | ofNat _ => exact hpow
    | negSucc _ => exact (Equiv.inv (T ⟶ U.X)).bijective.comp hpow

end Langlands.GroupScheme
