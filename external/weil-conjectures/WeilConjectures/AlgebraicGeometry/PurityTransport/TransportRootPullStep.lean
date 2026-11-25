/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso

/-! # Compatibility of normalized root power transitions

## References

* Stacks 03PK
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.PurityTransport

private theorem rootComparison_transition (X : Scheme.{u}) (N m : ℕ)
    (hN : 0 < N) (hm : 0 < m) :
    rootsOfUnitySheafPow X N m ≫ (rootComparison X N).hom =
      (rootComparison X (m * N)).hom ≫
        proEtaleRootsOfUnityTransition X N (m * N) hN (Nat.mul_pos hm hN)
          (dvd_mul_left N m) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology X) _ _
    (proEtaleRootsOfUnitySheaf X N).property
  change toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N)) ≫
      sheafifyMap (ProEt.topology X)
        (Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
          (CommRingCat.rootsOfUnityPow N m)) ≫ (rootComparison X N).hom.hom = _
  rw [← Category.assoc, ← toSheafify_naturality]
  ext U z
  apply (proEtaleRootsOfUnitySections X N U).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  have hleft := (rootComparison_existsUnique X N).exists.choose_spec U
    ((Functor.whiskerLeft ((ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
      (CommRingCat.rootsOfUnityPow N m)).app U z)
  have hright := roots_transition_value X N (m * N) hN (Nat.mul_pos hm hN)
    (dvd_mul_left N m) U
      ((rootComparison X (m * N)).hom.hom.app U
        ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z))
  have hnorm := (rootComparison_existsUnique X (m * N)).exists.choose_spec U z
  change proEtaleRootsOfUnitySections X (m * N) U
    ((rootComparison X (m * N)).hom.hom.app U
      ((toSheafify (ProEt.topology X) (rootsOfUnityPresheaf X (m * N))).app U z)) =
    z.down at hnorm
  rw [hnorm] at hright
  rw [Nat.mul_div_cancel _ hN] at hright
  exact (congrArg (fun x ↦ x.toMul.val) hleft).trans hright.symm

private theorem rootPull_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N m : ℕ) (hN : 0 < N) (hm : 0 < m) :
    (upperStar Ab.{u + 1} f).map (rootsOfUnitySheafPow Y N m) ≫ rootPull f N =
      rootPull f (m * N) ≫ rootsOfUnitySheafPow X N m := by
  unfold rootPull
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, rootComparison_transition Y N m hN hm,
    Functor.map_comp, Category.assoc]
  erw [reassoc_of% roots_inverse_transition f N (m * N) hN
    (Nat.mul_pos hm hN) (dvd_mul_left N m)]
  congr 2
  apply (cancel_mono (rootComparison X N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rootComparison_transition X N m hN hm, Iso.inv_hom_id_assoc]

private theorem rootPull_cast {X Y : Scheme.{u}} (f : X ⟶ Y)
    {N N' : ℕ} (h : N = N') :
    (upperStar Ab.{u + 1} f).map (eqToHom (congrArg (rootsOfUnitySheaf Y) h)) ≫
        rootPull f N' =
      rootPull f N ≫ eqToHom (congrArg (rootsOfUnitySheaf X) h) := by
  subst N'
  simp

/-- Normalized root pullback commutes with the successive power transitions. -/
theorem normalizedRootPull_step (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (upperStar Ab.{u + 1} f).map
        (eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow Y (ell ^ n) ell) ≫
      rootPull f (ell ^ n) =
    rootPull f (ell ^ (n + 1)) ≫
      eqToHom (by rw [pow_succ']) ≫ rootsOfUnitySheafPow X (ell ^ n) ell := by
  rw [Functor.map_comp, Category.assoc,
    rootPull_transition f (ell ^ n) ell
      (pow_pos (Fact.out : ell.Prime).pos n) (Fact.out : ell.Prime).pos,
    ← Category.assoc, rootPull_cast f (pow_succ' ell n), Category.assoc]

end AlgebraicGeometry.ProEtale.PurityTransport
