/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.Data.Int.GCD

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A prime-annihilated sheaf has invertible-order torsion when the prime is a unit
on the base field; otherwise invertible-order torsion forces the sheaf to be zero.
Source: Stacks Project, Tag 0GJA, proof, remark (a); elementary Bezout argument
and geometric stalk conservativity.
(blueprint: lemma-removing-finitely-many-points--1).

Proof: Stalk functors are additive, so r kills every stalk element. If r is a unit in
the global sections of Spec k, this same positive integer witnesses invertible-order
torsion. Otherwise, via the canonical isomorphism of those sections with k, r is zero
in k and the field has characteristic r. If a stalk element is killed by an integer n
invertible in these sections, r does not divide n. Since r is prime, r and n are
coprime, and Bezout's identity makes the element zero. All stalks are zero, so stalk
conservativity makes F zero. No constructibility or finiteness assumption is used. -/
theorem prime_annihilated_invertible_cases (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (r : ℕ) [Fact r.Prime]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : r • 𝟙 F = 0) :
    (IsUnit (r : Γ(Spec (.of k), ⊤)) →
      IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F) ∧
    (¬ IsUnit (r : Γ(Spec (.of k), ⊤)) →
      IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F → IsZero F) := by
  have : LocallySmall.{u} X.Etale := locallySmall_self _
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have hr (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
      (x : ↥(((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F)) : r • x = 0 := by
    have := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
    have h := congrArg (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).map) hF
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
    exact congrArg (fun t ↦ t.hom x) h
  constructor
  · intro hu
    exact ⟨fun Ω _ _ s x ↦ ⟨r, (Fact.out : r.Prime).pos, hu, hr Ω s x⟩⟩
  · intro hu hInv
    let e := (ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
    have hrk : ¬ IsUnit (r : k) := by
      intro hh
      apply hu
      simpa using hh.map e.symm.toMonoidHom
    have hrzero : (r : k) = 0 := by
      by_contra hh
      exact hrk (isUnit_iff_ne_zero.mpr hh)
    apply (IsZero.iff_id_eq_zero F).mpr
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro s
    have := (pointSmallEtale (X.algClosurePoint s)).sheafFiber_additive
      (A := ModuleCat.{u + 1} Λ)
    rw [CategoryTheory.Functor.map_id, Functor.map_zero]
    ext x
    obtain ⟨n, _, hnunit, hn⟩ := hInv.exists_isUnit_nsmul_eq_zero _ (X.algClosurePoint s) x
    have hnk : (n : k) ≠ 0 := by
      have hh : IsUnit (n : k) := by simpa using hnunit.map e.toMonoidHom
      exact hh.ne_zero
    have hndiv : ¬ r ∣ n := by
      rintro ⟨m, rfl⟩
      apply hnk
      simp [Nat.cast_mul, hrzero]
    have hc := (Fact.out : r.Prime).coprime_iff_not_dvd.mpr hndiv
    exact (nsmul_eq_zero_iff_of_coprime hc).mp ⟨hr _ (X.algClosurePoint s) x, hn⟩

end AlgebraicGeometry.Scheme
