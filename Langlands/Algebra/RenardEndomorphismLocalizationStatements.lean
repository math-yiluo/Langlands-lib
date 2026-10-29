import Langlands.Algebra.RenardEndomorphismLocalization

/-! # Kernel and power exhaustion of actual endomorphism localization -/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

/-- An element vanishes under the canonical localization map exactly when a power kills it.
This is an internal strengthening of the kernel inclusion in Renard A.III.1. -/
def KernelCriterionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V) (z : V),
      iota a z = 0 ↔ ∃ n : ℕ, (a ^ n) z = 0

/-- The kernel of the actual canonical map is the supremum of the ascending power kernels. -/
def KernelUnionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
      LinearMap.ker (iota a) = ⨆ n : ℕ, LinearMap.ker (a ^ n)

/-- Renard's injectivity assertion for the actual localization map, extended to rings. -/
def InjectivityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
      Function.Injective a → Function.Injective (iota a)

/-- The actual localization is the literal union of the inverse-power images of the
canonical image. No quotient identification or finite-generation premise is assumed. -/
def PowerExhaustionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
      (⋃ n : ℕ, Set.range ((localizedInv a ^ n).comp (iota a))) =
        (Set.univ : Set (Localized a))

/-- The four clauses over rings, with independent coefficient and source universes. -/
def KernelExhaustionStatement : Prop :=
  KernelCriterionStatement.{u, v} ∧ KernelUnionStatement.{u, v} ∧
    InjectivityStatement.{u, v} ∧ PowerExhaustionStatement.{u, v}

/-- The exact field specialization of the four clauses. The source states injectivity;
the kernel equalities and exhaustion in the canonical image are derived formulations. -/
def FieldKernelExhaustionStatement : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (a : Module.End k V),
      (∀ z : V, iota a z = 0 ↔ ∃ n : ℕ, (a ^ n) z = 0) ∧
        (LinearMap.ker (iota a) = ⨆ n : ℕ, LinearMap.ker (a ^ n)) ∧
        (Function.Injective a → Function.Injective (iota a)) ∧
        ((⋃ n : ℕ, Set.range ((localizedInv a ^ n).comp (iota a))) =
          (Set.univ : Set (Localized a)))

/-- Complete target: the general ring statements and their explicit field specialization. -/
def KernelExhaustionStatements : Prop :=
  KernelExhaustionStatement.{u, v} ∧ FieldKernelExhaustionStatement.{u, v}

end Langlands.Renard.EndomorphismLocalization
