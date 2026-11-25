/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Data.Int.GCD

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Prime annihilation gives primary torsion for that prime, and a sheaf primary for
another prime must be zero.
Source: Stacks Project, Tag 0GJA, proof, primary assertion; elementary Bezout argument
and geometric stalk conservativity.
(blueprint: lemma-removing-finitely-many-points--1).

Proof: Applying a geometric stalk functor to r times the identity shows that r kills
all stalk elements, so exponent one witnesses r-primary torsion. If p is a different
prime and an element is killed by p^n, then r and p^n are coprime. Bezout's identity
makes this element zero. Thus every geometric stalk is zero, and conservativity of
geometric stalks makes F zero. This also covers the zero sheaf and the empty scheme. -/
theorem prime_annihilated_primary_cases (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} (r : ℕ) [Fact r.Prime]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : r • 𝟙 F = 0) :
    IsPrimaryTorsionSheaf Λ F r ∧
      (∀ (p : ℕ) [Fact p.Prime], r ≠ p → IsPrimaryTorsionSheaf Λ F p → IsZero F) := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have hr (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥(((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F)) : r • x = 0 := by
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    have h := congrArg (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map) hF
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    exact congrArg (fun t ↦ t.hom x) h
  refine ⟨fun Ω _ _ s x ↦ ⟨1, by simpa using hr Ω s x⟩, ?_⟩
  intro p _ hrp hp
  apply (IsZero.iff_id_eq_zero F).mpr
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro s
  have := (pointSmallEtale (X.algClosurePoint s)).sheafFiber_additive
    (A := ModuleCat.{u + 1} Λ)
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  ext x
  obtain ⟨n, hn⟩ := hp _ (X.algClosurePoint s) x
  have hc : r.Coprime (p ^ n) := by
    simpa using Nat.coprime_pow_primes 1 n (Fact.out : r.Prime) (Fact.out : p.Prime) hrp
  exact (nsmul_eq_zero_iff_of_coprime hc).mp ⟨hr _ (X.algClosurePoint s) x, hn⟩

end AlgebraicGeometry.Scheme
