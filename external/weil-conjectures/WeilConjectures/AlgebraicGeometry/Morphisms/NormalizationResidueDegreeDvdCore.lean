/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.Coset.Card

/-! # The Galois arithmetic part of normalization residue-degree divisibility

The geometric comparison with normalization is
supplied separately; the Galois action is an explicit hypothesis here.

## References

* Stacks Project, Tag 09EB

## Implementation details

The statement is for finite flat extensions of domains, more general than the DVR case of
the source.
-/

@[expose] public section
universe u v w
namespace AlgebraicGeometry.Scheme

/-- The residue degree of a prime in a finite flat Galois extension of domains divides
any finite group containing its Galois group as a subgroup. -/
theorem normalization_residue_degree_dvd_core
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Module.Finite R S] [Module.Flat R S]
    (G : Type w) [Group G] [Finite G] (T : Subgroup G)
    [MulSemiringAction T S] [IsGaloisGroup T R S]
    (q : Ideal S) [q.IsPrime] : q.inertiaDeg R ∣ Nat.card G := by
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (q.under R) S T
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (q.under R) q T] at h
  have hd : q.inertiaDeg R ∣ Nat.card T := by
    rw [← h, ← Nat.mul_assoc]
    exact dvd_mul_left _ _
  exact hd.trans T.card_subgroup_dvd_card

end AlgebraicGeometry.Scheme
