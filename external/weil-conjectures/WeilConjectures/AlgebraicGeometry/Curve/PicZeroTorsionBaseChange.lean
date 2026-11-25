/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-!
# Degree-zero Picard points under algebraically closed field extension

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case and the
Jacobian point comparison in the affine case (blueprint: lem-sc-piczero-torsion-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option autoImplicit false

/-- The canonical comparison on degree-zero Picard groups is injective and every
prime-to-characteristic torsion point after extension lifts to a torsion point before extension.

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper degree-one
comparison and affine Jacobian correction (blueprint:
corollary-torsion-jacobian-field-extension--2).

Proof: a proper smooth connected curve over an algebraically closed field is geometrically
integral and smooth of relative dimension one. Jacobian representability identifies its
Picard degree-zero subgroup with the rational points of its Jacobian. Compatibility of the
representing Picard functor with base change identifies the specified pullback homomorphism
with extension of rational points of this same Jacobian. The latter is injective: two
morphisms from Spec k equal after Spec k' have the same image point and the same residue-field
map, since k to k' is injective. For torsion, n is positive and prime to the characteristic,
so clause (c) of the abelian-variety estimate makes extension bijective on the rational
points of the finite etale n-torsion subgroup scheme. Identify those points with the elements
whose nth power is one, and transport through the natural Jacobian identifications. The
hypotheses on G, G', and j merely choose subgroup models and spell out that canonical map.
For n=1 torsion consists of the identity; for a genus-zero curve both groups are trivial.
The conclusion does not assert anything about an affine quotient or a boundary subgroup. -/
theorem picZero_torsion_base_change
    {k k' : Type u} [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] [Algebra k k']
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f]
    (G : Subgroup X.Pic) (hG : (G : Set X.Pic) = f.picZero)
    (G' : Subgroup (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
    (hG' : (G' : Set (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic) =
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).picZero)
    (j : G →* G')
    (hj : ∀ L : G, (j L).val = Scheme.Pic.mapHom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L.val)
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Function.Injective j ∧ ∀ y : G', y ^ n = 1 → ∃ x : G, x ^ n = 1 ∧ j x = y :=
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  by
  classical
  obtain ⟨J, hJ, hA, e, e', hcomp⟩ :=
    pic_zero_jacobian_point_comparison f G hG G' hG' j hj
  let := hJ
  let := hA
  let (S : Over (Spec (.of k))) : CommGroup (S ⟶ J) := CategoryTheory.Hom.commGroup
  let T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hinj : Function.Injective j := by
    intro x z hxz
    apply e.injective
    apply Over.OverMorphism.ext
    apply Scheme.SpecMap_comp_injective (CommRingCat.ofHom (algebraMap k k'))
    have h := congrArg (fun a ↦ (e' a).left) hxz
    simpa only [hcomp, Over.comp_left, Over.toUnit_left, Over.mk_left, Over.mk_hom] using h
  refine ⟨hinj, ?_⟩
  intro y hy
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun h ↦ hn (by simp [h]))
  have hnp : ¬ ringChar k ∣ n :=
    (CharP.cast_eq_zero_iff k (ringChar k) n).not.mp hn
  have hy' : e' y ≫ (𝟙 J ^ n) = 1 := by
    rw [MonObj.comp_pow, Category.comp_id, ← map_pow, hy, map_one]
  have hmem : e' y ∈ (IsMonHom.monoidHom (𝟙 J ^ n) T).ker := hy'
  rw [← GrpObj.range_monoidHom_kerι] at hmem
  obtain ⟨t, ht⟩ := hmem
  obtain ⟨s, hs⟩ :=
    ((abelianVariety_estimate_of_isAlgClosed (ringChar k) J).2.1 n hnpos hnp k').2 t
  let a := s ≫ GrpObj.kerι (𝟙 J ^ n)
  have hapow : a ^ n = 1 := by
    rw [← Category.comp_id a, ← MonObj.comp_pow]
    dsimp only [a]
    rw [Category.assoc, GrpObj.kerι_comp]
    simp only [← Category.assoc]
    congr 1
    exact CartesianMonoidalCategory.toUnit_unique _ _
  let x := e.symm a
  have hx : x ^ n = 1 := by
    apply e.injective
    change e (e.symm a ^ n) = e 1
    simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using hapow
  refine ⟨x, hx, e'.injective ?_⟩
  rw [hcomp]
  change toUnit T ≫ e (e.symm a) = e' y
  rw [MulEquiv.apply_symm_apply]
  dsimp only [a]
  rw [← Category.assoc]
  have hs' : toUnit T ≫ s = t := hs
  exact (congrArg (fun q ↦ q ≫ GrpObj.kerι (𝟙 J ^ n)) hs').trans ht

end AlgebraicGeometry
