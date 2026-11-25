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
# Exactness of the degree-zero part of an away localization

Source: Stacks Project, Constructions, Lemma 01M7 and Algebra, Section 00JM.
(blueprint: lem-sc-p1-away-degreezero-exact)
-/

@[expose] public section

universe u

open MvPolynomial LocalizedModule

namespace LocalizedModule

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An exact graded sequence stays exact on equal-degree fractions after inverting a
positive homogeneous element, and this exactness transfers along additive chart identifications.

Source: Stacks Project, Constructions, Lemma 01M7, final paragraph; Algebra,
Section 00JM. (blueprint: lem-sc-p1-away-degreezero-exact)

Proof: If f=0, its powers include zero, so every localized module is zero.
Injectivity of alpha then makes every A_j zero, proving all three assertions.
Otherwise each f^m is nonzero and homogeneous of degree m*d. Uniqueness of
homogeneous degrees in the polynomial ring implies that a denominator f^m
in degree n has n=m*d.

Localize the given exact sequence at the powers of f. Localization preserves
injectivity, exactness and surjectivity. On each localized module define the
integer-degree e subgroup by the fractions y/f^m with y in degree e+m*d.
Sums have a common denominator, so these are additive subgroups. Decomposing
a numerator into its finitely many homogeneous components proves that these
subgroups span the localization. For independence, take a finite relation
among distinct degrees, put every term over f^N, and clear the relation by
another f^L. The resulting numerators have distinct degrees e+(N+L)*d;
internality of the original grading makes each zero. Hence each original
fraction was zero, and the localized decomposition is internal.

The localized maps preserve this grading by the degree-preserving hypotheses.
For a homogeneous target, decompose a localized preimage and keep its component
of degree zero. Independence in the target makes that component map to the
given target. This proves surjectivity on degree zero, and gives the same lift
for a degree-zero element in the kernel. Injectivity is inherited from ordinary
localization. By the denominator degree calculation, the degree-zero subgroup
is precisely degreeZeroFractions: its numerators have degree m*d, which is
nonnegative, and its denominators have the same degree. Finally every localized
element has a powers-of-f denominator. The fraction formulas identify i and q
with the restrictions of the localized maps. The injective alpha maps, with
their prescribed ranges, transport injectivity, exactness and surjectivity to A.
-/
theorem proj_away_degreeZero_exact
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
    (hinj : Function.Injective phi) (hexact : Function.Exact phi psi)
    (hsurj : Function.Surjective psi)
    (i : A 0 →+ A 1) (q : A 1 →+ A 2)
    (hi : ∀ (m : ℕ) (y : M 0) (s : A 0),
      alpha 0 s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 1 (i s) = mk (phi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))
    (hq : ∀ (m : ℕ) (y : M 1) (s : A 1),
      alpha 1 s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
      alpha 2 (q s) = mk (psi y) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) :
    Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q := by
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
  have injF : Function.Injective F :=
    IsLocalizedModule.map_injective T _ _ phi hinj
  have exFG : Function.Exact F G := IsLocalizedModule.map_exact T _ _ _ phi psi hexact
  have surjG : Function.Surjective G :=
    IsLocalizedModule.map_surjective T _ _ psi hsurj
  refine ⟨?_, ?_, ?_⟩
  · intro s t h
    apply (halpha 0).1
    apply injF
    rw [comm_i, comm_i, h]
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
  · intro s
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
