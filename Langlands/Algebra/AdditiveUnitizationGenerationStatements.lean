import Mathlib.Algebra.Algebra.Unitization
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Internal additive stable-generation comparisons for integer unitization

The targets range over actual additive subgroups, without a scalar-linearity
condition. The source's finiteness conventions require separate comparisons.
-/

set_option autoImplicit false

namespace Langlands.Algebra.AdditiveUnitizationGeneration

universe uA uM

/-- Finite generation of a unitized submodule is finite generation among all
additive subgroups stable under the original additive representation. -/
def SubmoduleGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [Module (Unitization ℤ A) M]
    (ρ : A →ₙ+* AddMonoid.End M),
    (∀ (u : Unitization ℤ A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    ∀ Q : Submodule (Unitization ℤ A) M,
      Q.FG ↔ ∃ S : Finset M, (↑S : Set M) ⊆ Q ∧
        ∀ P : AddSubgroup M,
          (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
          (↑S : Set M) ⊆ P →
            Submodule.toAddSubgroup (R := Unitization ℤ A) Q ≤ P

/-- Finiteness of the unitized module is generation by a finite set among
all additive subgroups stable under the original additive representation. -/
def ModuleGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [Module (Unitization ℤ A) M]
    (ρ : A →ₙ+* AddMonoid.End M),
    (∀ (u : Unitization ℤ A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    (Module.Finite (Unitization ℤ A) M ↔
      ∃ S : Finset M, ∀ P : AddSubgroup M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P → P = ⊤)

/-- Noetherianity of the unitized module is finite stable generation of
every stable additive subgroup, with the universal property explicit. -/
def NoetherianGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [Module (Unitization ℤ A) M]
    (ρ : A →ₙ+* AddMonoid.End M),
    (∀ (u : Unitization ℤ A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    (IsNoetherian (Unitization ℤ A) M ↔
      ∀ P : AddSubgroup M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : AddSubgroup M,
            (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
            (↑S : Set M) ⊆ Q → P ≤ Q)

/-- The submodule, whole-module and Noetherian comparisons, in that order. -/
def AdditiveUnitizationGenerationStatement : Prop :=
  SubmoduleGenerationStatement.{uA, uM} ∧
    ModuleGenerationStatement.{uA, uM} ∧
    NoetherianGenerationStatement.{uA, uM}

end Langlands.Algebra.AdditiveUnitizationGeneration
