/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.LinearAlgebra.ExteriorLocalizationKernelTorsion

/-! # Localization of exterior powers

Source: Stacks Project, Tag 0C6F, Lemma 10.13.6 (localization of tensor, symmetric,
and exterior algebras), restricted to the homogeneous part of degree n.
(blueprint: new-v2-generic-exterior-power-localization). -/

@[expose] public section
set_option autoImplicit false
universe u v w z

namespace exteriorPower

private theorem localizedWedge_surj
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    {M : Type w} {N : Type z} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (g : (⋀[R]^n M) →ₗ[R] (⋀[A]^n N))
    (hg : ∀ a : Fin n → M,
      g (exteriorPower.ιMulti R n a) =
        exteriorPower.ιMulti A n (fun i => f (a i))) :
    ∀ y : ⋀[A]^n N, ∃ p : (⋀[R]^n M) × S, p.2 • y = g p.1 := open scoped BigOperators in by
  classical
  intro y
  have hy : y ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := N))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    choose p hp using fun i => IsLocalizedModule.surj S f (a i)
    refine ⟨⟨exteriorPower.ιMulti R n (fun i => (p i).1), ∏ i, (p i).2⟩, ?_⟩
    rw [hg]
    change algebraMap R A (↑(∏ i, (p i).2) : R) • exteriorPower.ιMulti A n a = _
    simp only [map_prod, Submonoid.coe_finsetProd]
    rw [← AlternatingMap.map_smul_univ]
    congr 1
    funext i
    simpa only [Submonoid.smul_def, algebraMap_smul] using hp i
  | zero => exact ⟨⟨0, 1⟩, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨⟨x, s⟩, hx⟩ := hy
    obtain ⟨⟨x', s'⟩, hx'⟩ := hz
    refine ⟨⟨(s' : R) • x + (s : R) • x', s * s'⟩, ?_⟩
    change (s : R) • y = g x at hx
    change (s' : R) • z = g x' at hx'
    change ((s : R) * (s' : R)) • (y + z) = _
    rw [smul_add, mul_smul, mul_smul, smul_comm (s : R) (s' : R) y, hx, hx']
    simp only [map_add, map_smul]
  | smul c y _ hy =>
    obtain ⟨⟨x, s⟩, hx⟩ := hy
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj S c
    refine ⟨⟨r • x, t * s⟩, ?_⟩
    change (algebraMap R A (↑(t * s) : R)) • (c • y) = _
    change (algebraMap R A (s : R)) • y = g x at hx
    change c * algebraMap R A (t : R) = algebraMap R A r at ht
    rw [Submonoid.coe_mul, map_mul, mul_smul, smul_comm (algebraMap R A (s : R)) c y,
      ← mul_smul, mul_comm (algebraMap R A (t : R)) c, ht, hx]
    exact (g.map_smul r x).symm

/-- A map characterized on pure wedges localizes exterior powers when the underlying
module map and coefficient ring are localizations.

Source: Stacks Project, Tag 0C6F, Lemma 10.13.6; the degree-n exterior component.
(blueprint: new-v2-generic-exterior-power-localization).

Proof: Every element of S acts invertibly on the target, since it is an
A-module and A is the localization of R. A pure wedge in N has a denominator
obtained by multiplying the denominators of its entries. The wedge formula
for g then expresses that denominator multiple as an image. Span induction
extends the fraction expression to sums (multiply their denominators) and to
A-scalars (express the scalar itself as a fraction in R). Finally, apply
exists_smul_eq_zero_of_localized_wedge to x-y whenever g(x)=g(y); it supplies
the equality axiom of module localization. These three properties are exactly
IsLocalizedModule. The argument includes n=0, with empty denominator product 1,
and 0 in S. No freeness or finiteness is used.
-/
theorem isLocalizedModule_of_pure_wedge
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    {M : Type w} {N : Type z} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : ℕ)
    (g : (⋀[R]^n M) →ₗ[R] (⋀[A]^n N))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti A n (fun i => f (a i))) :
    IsLocalizedModule S g := by
  refine ⟨?_, localizedWedge_surj S f n g hg, ?_⟩
  · intro s
    rw [← (Algebra.lsmul R (A := A) R (⋀[A]^n N)).commutes]
    exact (IsLocalization.map_units A s).map _
  · intro x y hxy
    obtain ⟨s, hs⟩ := exists_smul_eq_zero_of_localized_wedge S f n g hg (x - y)
      (by rw [map_sub, hxy, sub_self])
    exact ⟨s, sub_eq_zero.mp ((smul_sub s x y).symm.trans hs)⟩

end exteriorPower
