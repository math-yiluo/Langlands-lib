/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Picard.Group

import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.PicardDecomposition
import WeilConjectures.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange

/-!
# Proper Picard torsion under algebraically closed extension

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case in degree
one (blueprint: lem-sc-proper-pic-torsion-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case in
degree one (blueprint: lem-sc-proper-pic-torsion-base-change).

Proof: the degree map takes values in the torsion-free group of integers, so an n-torsion
line bundle has degree zero. The representing Jacobian identifies degree-zero line bundles
with rational points and respects the group law. Jacobian base change identifies the
Jacobian of the base-changed curve with the scalar extension of the original Jacobian,
and its classifying-morphism equation identifies Picard pullback with extension of points.
As n is invertible, Jacobian n-torsion is finite etale. Over an algebraically closed field
such a scheme is a disjoint union of rational points; extending the field preserves exactly
these points. Thus the extension map on Jacobian n-torsion is bijective, and so is the map
on Picard n-torsion. In particular n = 1 gives the bijection of singleton identity groups.
No choice of bases or comparison of cardinalities is used to identify the canonical map. -/
theorem IsConnectedCurve.proper_pic_torsion_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0) :
    ∃ F : {L : C.Pic // L ^ n = 1} →
        {L : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic // L ^ n = 1},
      Function.Bijective F ∧ ∀ L, (F L).val = Scheme.Pic.map
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L.val := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let D := pullback f b
  let g : D ⟶ Spec (.of K) := pullback.snd f b
  have : IsConnectedCurve g := (baseChange_curve f).2.2.2.2.2 inferInstance
  have : Smooth g := inferInstanceAs (Smooth (pullback.snd f b))
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd f b))
  obtain ⟨G, hG, e, he, _⟩ := Scheme.Hom.exists_mulEquiv_prod_picZero f
  obtain ⟨G', hG', e', he', _⟩ := Scheme.Hom.exists_mulEquiv_prod_picZero g
  have torsion_mem (L : C.Pic) (hL : L ^ n = 1) : L ∈ G := by
    have hp := congrArg (fun x ↦ (e x).1) hL
    have hd : n * f.picDegree L = 0 := by
      simpa [map_pow, he, ← ofAdd_nsmul, nsmul_eq_mul, mul_comm] using hp
    have hz : f.picDegree L = 0 := (mul_eq_zero.mp hd).resolve_left (by
      exact_mod_cast NeZero.ne n)
    rw [← SetLike.mem_coe, hG]
    exact hz
  have torsion_mem' (L : D.Pic) (hL : L ^ n = 1) : L ∈ G' := by
    have hp := congrArg (fun x ↦ (e' x).1) hL
    have hd : n * g.picDegree L = 0 := by
      simpa [map_pow, he', ← ofAdd_nsmul, nsmul_eq_mul, mul_comm] using hp
    have hz : g.picDegree L = 0 := (mul_eq_zero.mp hd).resolve_left (by
      exact_mod_cast NeZero.ne n)
    rw [← SetLike.mem_coe, hG']
    exact hz
  let p := Scheme.Pic.mapHom (pullback.fst f b)
  have hdeg (L : C.Pic) : g.picDegree (p L) = f.picDegree L := by
    let : C.Over (Spec (.of k)) := ⟨f⟩
    let : D.Over (Spec (.of K)) := ⟨g⟩
    have : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
    have : QuasiSeparated (C ↘ Spec (.of k)) := inferInstanceAs (QuasiSeparated f)
    have := L.isInvertible
    rw [Scheme.Hom.picDegree_eq, Scheme.Hom.picDegree_eq]
    exact (Scheme.Modules.degree_congr K (fromSkeletonToSkeletonIso
      ((Scheme.Modules.pullback (pullback.fst f b)).obj
        ((fromSkeleton C.Modules).obj L.val)))).trans
          (Scheme.Modules.degree_pullback k K _)
  let j : G →* G' := {
    toFun L := ⟨p L, by
      rw [← SetLike.mem_coe, hG']
      change g.picDegree (p L.val) = 0
      rw [hdeg]
      have h := L.property
      rw [← SetLike.mem_coe, hG] at h
      exact h⟩
    map_one' := Subtype.ext (map_one p)
    map_mul' x y := Subtype.ext (map_mul p x.val y.val) }
  obtain ⟨hinj, hsurj⟩ := picZero_torsion_base_change f G hG G' hG' j
    (fun _ ↦ rfl) n hn
  let F : {L : C.Pic // L ^ n = 1} → {L : D.Pic // L ^ n = 1} :=
    fun L ↦ ⟨p L.val, by rw [← map_pow, L.property, map_one]⟩
  refine ⟨F, ⟨?_, ?_⟩, fun _ ↦ rfl⟩
  · intro L M h
    apply Subtype.ext
    have hj : j ⟨L.val, torsion_mem L.val L.property⟩ =
        j ⟨M.val, torsion_mem M.val M.property⟩ :=
      Subtype.ext (congrArg (fun z : {L : D.Pic // L ^ n = 1} ↦ z.val) h)
    exact congrArg (fun z : G ↦ z.val) (hinj hj)
  · intro L
    let y : G' := ⟨L.val, torsion_mem' L.val L.property⟩
    have hy : y ^ n = 1 := Subtype.ext L.property
    obtain ⟨x, hx, hxy⟩ := hsurj y hy
    refine ⟨⟨x.val, congrArg (fun z : G ↦ z.val) hx⟩, ?_⟩
    exact Subtype.ext (congrArg (fun z : G' ↦ z.val) hxy)

end AlgebraicGeometry
