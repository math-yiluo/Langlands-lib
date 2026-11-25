/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.AffineConormalSections

/-!
# A first order thickening with zero conormal is an isomorphism

Source: Stacks Project, Tags 04FE and 01R3.
(blueprint: lem-weil-pbc-first-order-thickening-conormal-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- A square-zero closed immersion is an isomorphism if its conormal module vanishes.
This is the ideal-theoretic part of (3) implies (2) in Tag 04FE; it does not require
any universal lifting property.
Source: Stacks Project, Tag 04FE, proof, and Tag 01R3 (2).
(blueprint: lem-weil-pbc-first-order-thickening-conormal-zero).
Proof: on any affine open U in X', let I be the kernel of the section map of i.
The affine conormal identification (01R3 (2)) identifies the conormal sections
on i⁻¹(U) with I/I². Zero conormal makes this quotient zero. The first order
hypothesis gives I² = 0 on U, so I itself is zero. This holds on every affine
open, hence the kernel ideal sheaf is zero. A closed immersion with zero kernel
ideal is an isomorphism, by IsClosedImmersion.isIso_iff_ker_eq_bot. This also
covers empty schemes and the zero ideal, without finiteness assumptions. -/
theorem firstOrderThickening_isIso_of_conormal_isZero {X X' : Scheme.{u}}
    (i : X ⟶ X') (hi : IsFirstOrderThickening i)
    (hC : IsZero ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)) :
    IsIso i := by
  have : IsClosedImmersion i := hi.1
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply Scheme.IdealSheafData.ext
  funext U
  let I := i.ker.ideal U
  obtain ⟨e, _⟩ := (Scheme.Modules.affine_conormal_sections i).2 U
    Γ(X', U.1) (RingEquiv.refl _) I (by simp [I, Scheme.Hom.ker_apply])
  have hsec : ∀ z : Γ((Scheme.Modules.tensorPullback i).obj i.ker.toModules,
      i ⁻¹ᵁ U.1), z = 0 := by
    intro z
    have heq := congrArg (fun φ ↦ φ.app (i ⁻¹ᵁ U.1) z) (hC.eq_of_src (𝟙 _) 0)
    simpa using heq
  have : Subsingleton Γ((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules), U.1) :=
    ⟨fun x y ↦ (hsec x).trans (hsec y).symm⟩
  have hI : Subsingleton I.Cotangent := e.toEquiv.subsingleton
  have hsq : I ^ 2 = ⊥ := congrArg (fun J : X'.IdealSheafData ↦ J.ideal U) hi.2
  have hidem := (Ideal.cotangent_subsingleton_iff I).mp hI
  change I = ⊥
  exact hidem.symm.trans (by simpa [pow_two] using hsq)

end AlgebraicGeometry
