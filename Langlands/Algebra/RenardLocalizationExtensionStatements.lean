import Langlands.Algebra.RenardEndomorphismLocalization

/-! # Inverse-power extensions characterize endomorphism localization -/

set_option autoImplicit false

universe u v x w

namespace Langlands.Renard.EndomorphismLocalization

/-- An actual injective extension exhausted by inverse powers has the localization
universal property, with an independent target universe. -/
def ExtensionConverseStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V) (M : Type x) [AddCommGroup M] [Module R M]
    (β : M ≃ₗ[R] M) (j : V →ₗ[R] M),
    Function.Injective j →
    (∀ z : V, j (a z) = β (j z)) →
    (Set.univ : Set M) =
      ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j) →
    HasUniversalProperty.{u, v, x, w} a β.toLinearMap j

/-- Such an extension has a unique comparison with the actual localization,
respecting the canonical map and the invertible operators. -/
def ExtensionComparisonStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V) (M : Type x) [AddCommGroup M] [Module R M]
    (β : M ≃ₗ[R] M) (j : V →ₗ[R] M),
    Function.Injective j →
    (∀ z : V, j (a z) = β (j z)) →
    (Set.univ : Set M) =
      ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j) →
    ∃! e : Localized a ≃ₗ[R] M,
      e.toLinearMap.comp (iota a) = j ∧
      ∀ z : Localized a, e (localizedEnd a z) = β (e z)

/-- The source's field case, including the canonical comparison consequence. -/
def FieldExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (a : Module.End k V) (M : Type x) [AddCommGroup M] [Module k M]
    (β : M ≃ₗ[k] M) (j : V →ₗ[k] M),
    Function.Injective j →
    (∀ z : V, j (a z) = β (j z)) →
    (Set.univ : Set M) =
      ⋃ n : ℕ, Set.range ((β.symm.toLinearMap ^ n).comp j) →
    HasUniversalProperty.{u, v, x, w} a β.toLinearMap j ∧
      ∃! e : Localized a ≃ₗ[k] M,
        e.toLinearMap.comp (iota a) = j ∧
        ∀ z : Localized a, e (localizedEnd a z) = β (e z)

/-- Closed statement aggregate for the converse and its actual comparison. -/
def LocalizationExtensionStatements : Prop :=
  ExtensionConverseStatement.{u, v, x, w} ∧
    ExtensionComparisonStatement.{u, v, x} ∧
    FieldExtensionStatement.{u, v, x, w}

end Langlands.Renard.EndomorphismLocalization
