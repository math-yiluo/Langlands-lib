/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.RingTheory.Localization.BaseChange

/-! # The kernel of exterior localization

Source: Stacks Project, Tag 0C6F, Lemma 10.13.6 (localization of tensor, symmetric,
and exterior algebras), restricted to the homogeneous part of degree n.
(blueprint: new-v2-exterior-localization-kernel-torsion). -/

@[expose] public section
set_option autoImplicit false
universe u v w z t

namespace exteriorPower

open scoped BigOperators TensorProduct

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (S : Submonoid R) [IsLocalization S A]
variable {M : Type w} {N : Type z} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (f : M →ₗ[R] N) [IsLocalizedModule S f]
variable {L : Type t} [AddCommGroup L] [Module A L] [Module R L] [IsScalarTower R A L]

private noncomputable def extendMulti (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => M) L →ₗ[R]
      MultilinearMap R (fun _ : Fin n => N) L := by
  classical
  induction n with
  | zero =>
    exact (MultilinearMap.constLinearEquivOfIsEmpty
      (R := R) (S := R) (M₁ := fun _ : Fin 0 => N) (M₂ := L)).toLinearMap.comp
      (MultilinearMap.constLinearEquivOfIsEmpty
        (R := R) (S := R) (M₁ := fun _ : Fin 0 => M) (M₂ := L)).symm.toLinearMap
  | succ n ih =>
    let T := MultilinearMap R (fun _ : Fin n => N) L
    letI : IsScalarTower R A T := ⟨fun r a b => by ext v; exact smul_assoc r a (b v)⟩
    letI : IsLocalizedModule S (LinearMap.id : T →ₗ[R] T) := isLocalizedModule_id S T A
    let post : (M →ₗ[R] MultilinearMap R (fun _ : Fin n => M) L) →ₗ[R] (M →ₗ[R] T) :=
      { toFun := fun b => ih.comp b
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }
    exact (multilinearCurryLeftEquiv R (fun _ : Fin (n+1) => N) L).symm.toLinearMap.comp
      ((IsLocalizedModule.map S f (LinearMap.id : T →ₗ[R] T)).comp
        (post.comp (multilinearCurryLeftEquiv R (fun _ : Fin (n+1) => M) L).toLinearMap))

private theorem extendMulti_apply (n : ℕ)
    (b : MultilinearMap R (fun _ : Fin n => M) L) (a : Fin n → M) :
    extendMulti (A := A) S f n b (fun i => f (a i)) = b a := by
  induction n with
  | zero =>
    simp only [extendMulti]
    exact congrArg b (Subsingleton.elim _ _)
  | succ n ih =>
    simp only [extendMulti, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, multilinearCurryLeftEquiv_symm_apply,
      LinearMap.uncurryLeft_apply, IsLocalizedModule.map_apply]
    change extendMulti (A := A) S f n (b.curryLeft (a 0))
      (fun i => f (a i.succ)) = b a
    rw [ih]
    exact congrArg b (Fin.cons_self_tail a)

private theorem extendMulti_alt (n : ℕ) (b : M [⋀^Fin n]→ₗ[R] L) :
    ∀ (a : Fin n → N) (i j : Fin n), a i = a j → i ≠ j →
      extendMulti (A := A) S f n b.toMultilinearMap a = 0 := by
  classical
  intro a i j heq hne
  choose p hp using fun x : N => IsLocalizedModule.surj S f x
  let m : Fin n → M := fun k => (p (a k)).1
  let s : Fin n → S := fun k => (p (a k)).2
  let d : S := ∏ k, s k
  apply (IsLocalization.map_units A d).smul_left_cancel.mp
  change (algebraMap R A (d : R)) • _ = (algebraMap R A (d : R)) • (0 : L)
  rw [algebraMap_smul, smul_zero]
  have hh := (extendMulti (A := A) S f n b.toMultilinearMap).map_smul_univ
    (fun k => (s k : R)) a
  have ha : (fun k => (s k : R) • a k) = fun k => f (m k) := by
    funext k
    exact hp (a k)
  rw [ha, extendMulti_apply] at hh
  have hm : m i = m j := by simp only [m, heq]
  change b m = _ at hh
  rw [b.map_eq_zero_of_eq m hm hne] at hh
  simpa only [d, Submonoid.coe_finsetProd] using hh.symm

variable [Module A N] [IsScalarTower R A N]

private noncomputable def extendAlt (n : ℕ) (b : M [⋀^Fin n]→ₗ[R] L) :
    N [⋀^Fin n]→ₗ[A] L := by
  classical
  let e := extendMulti (A := A) S f n b.toMultilinearMap
  exact {
    toFun := e
    map_update_add' := e.map_update_add
    map_update_smul' := fun a i c x => by
      have h := ((e.toLinearMap a i).extendScalarsOfIsLocalization S A).map_smul c x
      simpa only [LinearMap.extendScalarsOfIsLocalization_apply',
        MultilinearMap.toLinearMap_apply] using h
    map_eq_zero_of_eq' := extendMulti_alt S f n b }

end


/-- The kernel of the map on exterior powers induced by localization is S-torsion.

Source: Stacks Project, Tag 0C6F, Lemma 10.13.6, the injectivity part in degree n.
(blueprint: new-v2-exterior-localization-kernel-torsion).

Proof: Let L=A tensor exteriorPower R n M and let l be its canonical
localization map. Extend the alternating map l composed with the pure wedge map
from M to N one coordinate at a time. Currying separates one coordinate;
IsLocalizedModule.map extends its linear map to N; induction handles the remaining
coordinates. The extension agrees with the original map on tuples coming from M.
To prove alternation, choose one fraction representative for each element of N.
Equal coordinates have equal representatives. Multiply all denominators and use
multilinearity; the resulting tuple lies in the image of f and its original wedge
vanishes. The product denominator acts invertibly on L, so the extension vanishes.
Every R-linear coordinate map between A-modules is A-linear because A is a
localization. The exterior universal property therefore gives an A-linear map h
from the exterior power of N to L. The pure-wedge formula proves h composed with
g equals l, since pure wedges span. If g(x)=0 then l(x)=0, and the equality criterion
for module localization gives s in S with s*x=0. The induction starts with empty
tuples in degree zero. No injectivity of f, finiteness, freeness, or restriction on
characteristic is used.
-/
theorem exists_smul_eq_zero_of_localized_wedge
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    {M : Type w} {N : Type z} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (g : (⋀[R]^n M) →ₗ[R] (⋀[A]^n N))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti A n (fun i => f (a i))) :
    ∀ x : ⋀[R]^n M, g x = 0 → ∃ s : S, s • x = 0 := by
  classical
  let L := A ⊗[R] (⋀[R]^n M)
  let l : (⋀[R]^n M) →ₗ[R] L := TensorProduct.mk R A _ 1
  let b : M [⋀^Fin n]→ₗ[R] L := l.compAlternatingMap (exteriorPower.ιMulti R n)
  let e : N [⋀^Fin n]→ₗ[A] L := extendAlt S f n b
  let h : (⋀[A]^n N) →ₗ[A] L := exteriorPower.alternatingMapLinearEquiv e
  have hh : (h.restrictScalars R).comp g = l := by
    apply exteriorPower.linearMap_ext
    ext a
    change h (g (exteriorPower.ιMulti R n a)) = l (exteriorPower.ιMulti R n a)
    rw [hg]
    change exteriorPower.alternatingMapLinearEquiv e
      (exteriorPower.ιMulti A n (fun i => f (a i))) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change extendMulti (A := A) S f n b.toMultilinearMap (fun i => f (a i)) = _
    rw [extendMulti_apply]
    rfl
  intro x hx
  have hl : l x = 0 := by
    rw [← LinearMap.congr_fun hh x]
    simp [hx]
  exact (IsLocalizedModule.eq_zero_iff S l).mp hl

end exteriorPower
