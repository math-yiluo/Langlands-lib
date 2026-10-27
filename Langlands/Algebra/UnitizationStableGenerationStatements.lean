import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Internal stable-generation comparisons for a supplied unitized action

These targets use actual scalar-linear submodules and an explicit stability
condition. They do not identify the book's nonunital finiteness conventions.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationStableGeneration

universe uR uA uM

/-- Finite generation of an actual unitized submodule is generation by a finite
set among scalar-linear submodules stable under the original representation. -/
def SubmoduleGenerationStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA) (M : Type uM)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [Module (Unitization R A) M]
    [IsScalarTower R (Unitization R A) M]
    (ρ : A →ₙₐ[R] Module.End R M),
    (∀ (u : Unitization R A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    ∀ Q : Submodule (Unitization R A) M,
      Q.FG ↔ ∃ S : Finset M, (↑S : Set M) ⊆ Q ∧
        ∀ P : Submodule R M,
          (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
          (↑S : Set M) ⊆ P → Q.restrictScalars R ≤ P

/-- The whole ordinary unitized module is finite exactly when a finite set is
contained in no proper scalar-linear stable submodule. -/
def ModuleGenerationStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA) (M : Type uM)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [Module (Unitization R A) M]
    [IsScalarTower R (Unitization R A) M]
    (ρ : A →ₙₐ[R] Module.End R M),
    (∀ (u : Unitization R A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    (Module.Finite (Unitization R A) M ↔
      ∃ S : Finset M, ∀ P : Submodule R M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        (↑S : Set M) ⊆ P → P = ⊤)

/-- Noetherianity of the ordinary unitized module is finite stable generation
of every scalar-linear stable submodule, with the universal property explicit. -/
def NoetherianGenerationStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA) (M : Type uM)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [AddCommGroup M] [Module R M] [Module (Unitization R A) M]
    [IsScalarTower R (Unitization R A) M]
    (ρ : A →ₙₐ[R] Module.End R M),
    (∀ (u : Unitization R A) (m : M),
      u • m = u.fst • m + ρ u.snd m) →
    (IsNoetherian (Unitization R A) M ↔
      ∀ P : Submodule R M,
        (∀ (a : A) (m : M), m ∈ P → ρ a m ∈ P) →
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : Submodule R M,
            (∀ (a : A) (m : M), m ∈ Q → ρ a m ∈ Q) →
            (↑S : Set M) ⊆ Q → P ≤ Q)

/-- The submodule, whole-module and Noetherian comparisons, in that order. -/
def UnitizationStableGenerationStatement : Prop :=
  SubmoduleGenerationStatement.{uR, uA, uM} ∧
    ModuleGenerationStatement.{uR, uA, uM} ∧
    NoetherianGenerationStatement.{uR, uA, uM}

end Langlands.Algebra.UnitizationStableGeneration
