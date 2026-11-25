/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison

/-! # Invertibility of normalized finite root pullback

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

private theorem globalPrimeUnit (Y : Scheme.{u}) (ell : ℕ)
    [∀ y : Y, Invertible (ell : Y.residueField y)] : IsUnit (ell : Γ(Y, ⊤)) := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ
  intro y hy
  rw [map_natCast]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (Y.residue y).hom (ell : Y.presheaf.stalk y) ≠ 0
  simpa only [map_natCast] using
    (isUnit_of_invertible (ell : Y.residueField y)).ne_zero

/-- The normalized root inverse image is invertible at every prime-power level. -/
theorem normalizedRootPull_isIso (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (n : ℕ) :
    IsIso (rootPull f (ell ^ n)) := by
  have hn : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  have hY : IsUnit ((ell ^ n : ℕ) : Γ(Y, ⊤)) := by
    simpa only [Nat.cast_pow] using (globalPrimeUnit Y ell).pow n
  have hX : IsUnit ((ell ^ n : ℕ) : Γ(X, ⊤)) := by
    simpa only [Nat.cast_pow] using (globalPrimeUnit X ell).pow n
  let A := ULift.{u + 1} (ZMod (ell ^ n))
  have hA : ((ell ^ n : ℕ) : A) = 0 := by
    apply ULift.ringEquiv.injective
    simp only [map_natCast, map_zero, ZMod.natCast_self]
  have h := rootComparison_square A (ell ^ n) hn hA f hY hX
  have hi : IsIso ((proEtaleSheafInverseImage f Ab.{u + 1}).map
      (cartierRootsIso Y (ell ^ n) hn hY).hom ≫
      proEtaleRootsOfUnityInverseImageMap f (ell ^ n)) := by
    rw [h]
    infer_instance
  have : IsIso (proEtaleRootsOfUnityInverseImageMap f (ell ^ n)) :=
    IsIso.of_isIso_comp_left
      ((proEtaleSheafInverseImage f Ab.{u + 1}).map
        (cartierRootsIso Y (ell ^ n) hn hY).hom) _
  unfold rootPull
  infer_instance

end AlgebraicGeometry.ProEtale.PurityTransport
