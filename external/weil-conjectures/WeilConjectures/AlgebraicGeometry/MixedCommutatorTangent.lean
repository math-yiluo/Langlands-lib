/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Comparison

/-!
# Mixed commutators of infinitesimal matrix points

Source: Milne, Algebraic Groups (2017), Chapter 10, differential of multiplication and
commutator (blueprint: `def-wf-lie-algebra-derivation`).

An arbitrary finite basis identifies GL(V) with the general linear group scheme. The ring
`DualNumber (DualNumber k)` is k[ε,δ]/(ε²,δ²), with coordinates 1, ε, δ, εδ.
-/

@[expose] public section

universe u v

open CategoryTheory TrivSqZeroExt
open scoped MonObj Matrix commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

namespace AlgebraicGeometry.GeneralLinearGroup

variable {k : Type u} [Field k] {G : Over (Spec (.of k))} [GrpObj G]

/-- The image under a rational representation `r` of the tangent point of `x` is `1 + ε dr(x)`. -/
theorem RationalHom.points_tangentPoint {m : Type u} [Fintype m] [DecidableEq m]
    (r : RationalHom G m) [IsMonHom r] (x : GrpObj.Lie G) :
    r.points (DualNumber k) (GrpObj.tangentPoint x) = dualUnit (r.differential x) := by
  apply Units.ext
  rw [coe_dualUnit, differential_eq_map_snd]
  refine Matrix.eq_one_add_map_inr_of_map_fst_eq_one ?_
  have h := congrArg (fun g : GL m k ↦ (g : Matrix m m k))
    (r.map_points (fstHom k k k) (GrpObj.tangentPoint x))
  rw [(mem_tangentGroup _).1 (GrpObj.tangentPoint_mem_tangentGroup x), map_one,
    Units.val_one] at h
  refine Matrix.ext fun i j ↦ ?_
  have hij := congrFun₂ h i j
  rw [Matrix.GeneralLinearGroup.map_apply] at hij
  exact hij

/-- A point of a subgroup scheme of `GL_n` with values in `k[ε]` whose matrix is `1 + εX` reduces
to the identity. -/
theorem mem_tangentGroup_of_homMulEquiv_comp_eq_dualUnit {n : Type u} [Fintype n]
    [DecidableEq n] (i : G ⟶ AlgebraicGeometry.GeneralLinearGroup n k) [IsSubgroupScheme i]
    {x : AlgebraicGeometry.points G (DualNumber k)} {X : Matrix n n k}
    (hx : homMulEquiv n k (DualNumber k) (x ≫ i) = dualUnit X) : x ∈ tangentGroup G := by
  rw [mem_tangentGroup]
  refine IsSubgroupScheme.injective_comp (i := i) k ?_
  refine (homMulEquiv n k k).injective ?_
  change homMulEquiv n k k (points.map G (fstHom k k k) x ≫ i) =
    homMulEquiv n k k ((1 : AlgebraicGeometry.points G k) ≫ i)
  rw [points.map, Category.assoc, homMulEquiv_specMap_comp, hx, MonObj.one_comp, map_one]
  exact map_fstHom_dualUnit X

/-- The `k`-algebra map `k[ε] → k[ε][δ]`, `ε ↦ ε`. -/
private theorem dualNumberLift_inl_eps
    (h : (inl DualNumber.eps : DualNumber (DualNumber k)) * inl DualNumber.eps = 0) :
    (dualNumberLift k (inl DualNumber.eps : DualNumber (DualNumber k)) h).toRingHom =
      inlHom (DualNumber k) (DualNumber k) := by
  ext : 1
  · ext x : 1
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact algebraMap_eq_inl' _ _ _ x
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualNumberLift_apply, DualNumber.fst_eps,
      DualNumber.snd_eps, map_zero, zero_add, one_smul]
    rfl

/-- The `k`-algebra map `k[ε] → k[ε][δ]`, `ε ↦ δ`. -/
private theorem dualNumberLift_eps :
    (dualNumberLift k (DualNumber.eps : DualNumber (DualNumber k))
      DualNumber.eps_mul_eps).toRingHom = DualNumber.mapRingHom (inlHom k k) := by
  ext : 1
  · ext x : 1
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [algebraMap_eq_inl']
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_inl, DualNumber.fst_mapRingHom, algebraMap_eq_inl, fst_inl]
      rfl
    · rw [snd_inl, DualNumber.snd_mapRingHom, algebraMap_eq_inl, snd_inl, map_zero]
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, dualNumberLift_apply, DualNumber.fst_eps,
      DualNumber.snd_eps, map_zero, zero_add, one_smul]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [DualNumber.fst_mapRingHom, DualNumber.fst_eps, DualNumber.fst_eps, map_zero]
    · rw [DualNumber.snd_mapRingHom, DualNumber.snd_eps, DualNumber.snd_eps, map_one]

/-- The `k`-algebra map `k[η] → k[ε][δ]`, `η ↦ εδ`, sends `1 + ηZ` to `1 + εδZ`. -/
private theorem coe_map_dualNumberLift_mixed_dualUnit {n : Type u} [Fintype n] [DecidableEq n]
    (Z : Matrix n n k) :
    (Matrix.GeneralLinearGroup.map (dualNumberLift k
      ((inl DualNumber.eps : DualNumber (DualNumber k)) * DualNumber.eps)
      dualNumber_eps_mul_eps_eq_zero).toRingHom (dualUnit Z) :
        Matrix n n (DualNumber (DualNumber k))) = 1 + Z.map (fun a ↦ inr (inr a)) := by
  rw [coe_map_dualNumberLift_dualUnit]
  congr 1
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
    smul_eq_mul, DualNumber.eps, DualNumber.eps, inl_mul_inr, smul_eq_mul, mul_one,
    algebraMap_eq_inl', algebraMap_eq_inl', Algebra.algebraMap_self, RingHom.id_apply,
    inr_mul_inl, op_smul_eq_mul, inr_mul_inl, op_smul_eq_mul, one_mul]

/-- Over a field, two infinitesimal points of a closed subgroup of GL(V) base change to
k[ε,δ]/(ε²,δ²); their commutator is 1 + εδ(XY - YX), and the corresponding dual-number point
belongs to the subgroup. The finite basis `b` is arbitrary, including the empty basis.

Source: Milne, Algebraic Groups (2017), Chapter 10, differential of multiplication and
commutator (blueprint: `def-wf-lie-algebra-derivation`).

Proof: base change the two points along the inner and outer dual-number inclusions. Their
commutator remains a subgroup point by def-sc-group-scheme-subgroup. The inverses of 1 + εX
and 1 + δY are 1 - εX and 1 - δY. Multiply the four factors using ε² = δ² = 0 to obtain
1 + εδ(XY - YX). The tangent vectors `x`, `y` of the subgroup have a bracket, whose tangent point
has matrix `1 + ε(XY - YX)` since the differential of the inclusion preserves brackets. -/
theorem mixedCommutator_tangent
    {n : Type u} {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Fintype n] [DecidableEq n] (b : Module.Basis n k V)
    (i : G ⟶ AlgebraicGeometry.GeneralLinearGroup n k) [IsClosedSubgroupScheme i]
    (X Y : Module.End k V) (x y : AlgebraicGeometry.points G (DualNumber k))
    (hx : homMulEquiv n k (DualNumber k) (x ≫ i) = dualUnit (LinearMap.toMatrix b b X))
    (hy : homMulEquiv n k (DualNumber k) (y ≫ i) = dualUnit (LinearMap.toMatrix b b Y)) :
    ∃ p q : AlgebraicGeometry.points G (DualNumber (DualNumber k)),
      homMulEquiv n k (DualNumber (DualNumber k)) (p ≫ i) =
        Matrix.GeneralLinearGroup.map (inlHom (DualNumber k) (DualNumber k))
          (dualUnit (LinearMap.toMatrix b b X)) ∧
      homMulEquiv n k (DualNumber (DualNumber k)) (q ≫ i) =
        Matrix.GeneralLinearGroup.map
          (DualNumber.mapRingHom (inlHom k k)) (dualUnit (LinearMap.toMatrix b b Y)) ∧
      (homMulEquiv n k (DualNumber (DualNumber k)) ((p * q * p⁻¹ * q⁻¹) ≫ i) :
        Matrix n n (DualNumber (DualNumber k))) =
        1 + (LinearMap.toMatrix b b (X * Y - Y * X)).map (fun a ↦ inr (inr a)) ∧
      ∃ z : AlgebraicGeometry.points G (DualNumber k),
        homMulEquiv n k (DualNumber k) (z ≫ i) =
          dualUnit (LinearMap.toMatrix b b (X * Y - Y * X)) := by
  set A := LinearMap.toMatrix b b X
  set B := LinearMap.toMatrix b b Y
  have hAB : LinearMap.toMatrix b b (X * Y - Y * X) = ⁅A, B⁆ := by
    rw [map_sub, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, Ring.lie_def]
  have he₁ : (inl DualNumber.eps : DualNumber (DualNumber k)) * inl DualNumber.eps = 0 := by
    rw [← inl_mul, DualNumber.eps_mul_eps, inl_zero]
  let φ₁ := dualNumberLift k (inl DualNumber.eps : DualNumber (DualNumber k)) he₁
  let φ₂ := dualNumberLift k (DualNumber.eps : DualNumber (DualNumber k)) DualNumber.eps_mul_eps
  have hcomp (φ : DualNumber k →ₐ[k] DualNumber (DualNumber k))
      (z : AlgebraicGeometry.points G (DualNumber k)) :
      homMulEquiv n k _ (points.map G φ z ≫ i) =
        Matrix.GeneralLinearGroup.map φ.toRingHom (homMulEquiv n k _ (z ≫ i)) := by
    rw [points.map, Category.assoc, homMulEquiv_specMap_comp]
  refine ⟨points.map G φ₁ x, points.map G φ₂ y, ?_, ?_, ?_, ?_⟩
  · rw [hcomp, hx, dualNumberLift_inl_eps he₁]
  · rw [hcomp, hy, dualNumberLift_eps]
  · have hc := commutatorElement_map_dualUnit he₁ DualNumber.eps_mul_eps
      dualNumber_eps_mul_eps_eq_zero A B
    rw [← hx, ← hy, ← hcomp, ← hcomp, commutatorElement_def] at hc
    rw [MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, GrpObj.inv_comp,
      map_mul, map_mul, map_mul, map_inv, map_inv, hc, coe_map_dualNumberLift_mixed_dualUnit, hAB]
  · obtain ⟨x', rfl⟩ := GrpObj.exists_tangentPoint_eq
      (mem_tangentGroup_of_homMulEquiv_comp_eq_dualUnit i hx)
    obtain ⟨y', rfl⟩ := GrpObj.exists_tangentPoint_eq
      (mem_tangentGroup_of_homMulEquiv_comp_eq_dualUnit i hy)
    have hdx : RationalHom.differential i x' = A := by
      refine dualUnit_injective ?_
      rw [← RationalHom.points_tangentPoint, RationalHom.points_apply, hx]
    have hdy : RationalHom.differential i y' = B := by
      refine dualUnit_injective ?_
      rw [← RationalHom.points_tangentPoint, RationalHom.points_apply, hy]
    refine ⟨GrpObj.tangentPoint ⁅x', y'⁆, ?_⟩
    rw [← RationalHom.points_apply, RationalHom.points_tangentPoint, LieHom.map_lie, hdx, hdy,
      hAB]

end AlgebraicGeometry.GeneralLinearGroup
