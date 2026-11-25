/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.Algebra.Module.AwayDegreeZeroLift

/-!
# Exact pairs on equal-degree fractions

Source: Stacks Project, Tag 01M7; Algebra, Tag 00JM.
(blueprint: lem-sc-p1-away-degreezero-exact-pair)
-/

@[expose] public section

universe u

open MvPolynomial LocalizedModule

namespace LocalizedModule

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Localization and degree zero preserve exact pairs, with either endpoint property when given.
Source: Stacks Project, Tag 01M7, final paragraph; Algebra, Tag 00JM.
(blueprint: lem-sc-p1-away-degreezero-exact-pair).

Proof: If f is zero, all three localized modules vanish and injective chart maps
make all three chart groups zero. Otherwise localize the exact pair at powers of f.
Give the localization degree e part consisting of fractions y/f^m with y in degree
e+m*d. Common denominators prove closure under addition. Homogeneous decomposition
of numerators proves spanning. For independence, clear denominators in a finite
relation; after multiplication by a further power of f, the numerators have distinct
degrees, and internality makes every numerator zero. The localized grading is
therefore internal. The maps preserve degrees. To lift a degree-zero kernel element,
use ordinary localized exactness and take the degree-zero component of a preimage;
internality in the middle module makes its image the desired element. Injectivity
is inherited from ordinary localization when phi is injective. If psi is surjective,
the same homogeneous-component argument gives a degree-zero preimage of every target.
A nonzero f^m has degree m*d, so the degree-zero parts are exactly the stipulated
degreeZeroFractions. Transport these assertions along alpha using its injectivity,
range equality, and the two fraction formulas. The exactness argument does not need
either endpoint property. -/
theorem proj_away_degreeZero_exact_pair
    (k : Type u) [Field k]
    (M : Fin 3 → Type u) [∀ j, AddCommGroup (M j)]
    [∀ j, Module (MvPolynomial (Fin 2) k) (M j)]
    (𝓜 : ∀ j, ℤ → AddSubgroup (M j))
    (h𝓜 : ∀ j, DirectSum.IsInternal (𝓜 j))
    (hsmul : ∀ (j : Fin 3) (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M j),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 j z → a • y ∈ 𝓜 j (n + z))
    (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
    (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
    (A : Fin 3 → Type u) [∀ j, AddCommGroup (A j)]
    (alpha : ∀ j, A j →+ LocalizedModule.Away f (M j))
    (halpha : ∀ j, Function.Injective (alpha j) ∧
      Set.range (alpha j) = degreeZeroFractions
        (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
        (fun n : ℕ ↦ (𝓜 j n : Set (M j))) (Submonoid.powers f))
    (phi : M 0 →ₗ[MvPolynomial (Fin 2) k] M 1)
    (psi : M 1 →ₗ[MvPolynomial (Fin 2) k] M 2)
    (hphi : ∀ (z : ℤ) (y : M 0), y ∈ 𝓜 0 z → phi y ∈ 𝓜 1 z)
    (hpsi : ∀ (z : ℤ) (y : M 1), y ∈ 𝓜 1 z → psi y ∈ 𝓜 2 z)
    (hexact : Function.Exact phi psi)
    (i : A 0 →+ A 1) (q : A 1 →+ A 2)
    (hi : ∀ (m : ℕ) (y : M 0) (s : A 0),
      alpha 0 s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 (i s) = mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (m : ℕ) (y : M 1) (s : A 1),
      alpha 1 s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 (q s) = mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    Function.Exact i q ∧
      (Function.Injective phi → Function.Injective i) ∧
      (Function.Surjective psi → Function.Surjective q) := by
  have _ := hd
  let T := Submonoid.powers f
  let F := IsLocalizedModule.map T (mkLinearMap T (M 0)) (mkLinearMap T (M 1)) phi
  let G := IsLocalizedModule.map T (mkLinearMap T (M 1)) (mkLinearMap T (M 2)) psi
  have comm_i (s : A 0) : F (alpha 0 s) = alpha 1 (i s) := by
    obtain ⟨y, t, ht⟩ := (show ∀ x : LocalizedModule.Away f (M 0), ∃ y t, mk y t = x from
      fun x ↦ induction_on (fun y t ↦ ⟨y, t, rfl⟩) x) (alpha 0 s)
    obtain ⟨m, hm⟩ := t.property
    have he : t = (⟨f ^ m, ⟨m, rfl⟩⟩ : T) := Subtype.ext hm.symm
    subst t
    rw [← ht]
    exact (IsLocalizedModule.map_LocalizedModules T phi y _).trans (hi m y s ht.symm).symm
  have comm_q (s : A 1) : G (alpha 1 s) = alpha 2 (q s) := by
    obtain ⟨y, t, ht⟩ := (show ∀ x : LocalizedModule.Away f (M 1), ∃ y t, mk y t = x from
      fun x ↦ induction_on (fun y t ↦ ⟨y, t, rfl⟩) x) (alpha 1 s)
    obtain ⟨m, hm⟩ := t.property
    have he : t = (⟨f ^ m, ⟨m, rfl⟩⟩ : T) := Subtype.ext hm.symm
    subst t
    rw [← ht]
    exact (IsLocalizedModule.map_LocalizedModules T psi y _).trans (hq m y s ht.symm).symm
  have mem_alpha (j : Fin 3) (s : A j) : alpha j s ∈ degreeZeroFractions
      (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
      (fun n : ℕ ↦ (𝓜 j n : Set (M j))) T := by
    rw [← (halpha j).2]
    exact ⟨s, rfl⟩
  have exFG : Function.Exact F G := IsLocalizedModule.map_exact T _ _ _ phi psi hexact
  refine ⟨?_, ?_, ?_⟩
  · intro s
    constructor
    · intro hs
      have hz : G (alpha 1 s) = 0 := by rw [comm_q, hs, map_zero]
      obtain ⟨y, hy⟩ := (exFG (alpha 1 s)).1 hz
      obtain ⟨z, hzmem, hzeq⟩ := away_degreeZero_lift k (M 0) (M 1)
        (𝓜 0) (𝓜 1) (h𝓜 0) (h𝓜 1) (hsmul 1) f d hf
        phi hphi (alpha 1 s) (mem_alpha 1 s) ⟨y, hy⟩
      rw [← (halpha 0).2] at hzmem
      obtain ⟨t, ht⟩ := hzmem
      refine ⟨t, (halpha 1).1 ?_⟩
      rw [← comm_i, ht]
      exact hzeq
    · rintro ⟨t, rfl⟩
      apply (halpha 2).1
      rw [map_zero, ← comm_q, ← comm_i]
      exact (exFG (F (alpha 0 t))).2 ⟨alpha 0 t, rfl⟩
  · intro hinj s t h
    apply (halpha 0).1
    have injF : Function.Injective F :=
      IsLocalizedModule.map_injective T _ _ phi hinj
    apply injF
    rw [comm_i, comm_i, h]
  · intro hsurj s
    have surjG : Function.Surjective G :=
      IsLocalizedModule.map_surjective T _ _ psi hsurj
    obtain ⟨y, hy⟩ := surjG (alpha 2 s)
    obtain ⟨z, hzmem, hzeq⟩ := away_degreeZero_lift k (M 1) (M 2)
      (𝓜 1) (𝓜 2) (h𝓜 1) (h𝓜 2) (hsmul 2) f d hf
      psi hpsi (alpha 2 s) (mem_alpha 2 s) ⟨y, hy⟩
    rw [← (halpha 1).2] at hzmem
    obtain ⟨t, ht⟩ := hzmem
    refine ⟨t, (halpha 2).1 ?_⟩
    rw [← comm_q, ht]
    exact hzeq

end LocalizedModule
