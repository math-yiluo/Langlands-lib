import Langlands.Algebra.IntegerNonUnitalSubmodule
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Finite stable generation for the original nonunital action

Internal comparison targets for the actual original stable additive subgroups
and the canonical integer-unitized module. Source finiteness conventions
require a separate comparison.
-/

set_option autoImplicit false

namespace Langlands.Algebra.IntegerOriginalSubmoduleGeneration

universe uA uM

/-- Finite generation of the actual unitized submodule is the finite-generator
universal property among the original stable additive subgroups. -/
def SubmoduleGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    ∀ P : NonUnitalSubmodule A M,
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        (NonUnitalSubmodule.intUnitizedOrderIso P).FG) ↔
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q

/-- The actual unitized module is finite exactly when a finite set generates
the whole carrier among the original stable additive subgroups. -/
def ModuleGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      Module.Finite (Unitization ℤ A) M) ↔
    ∃ S : Finset M, ∀ P : NonUnitalSubmodule A M,
      (↑S : Set M) ⊆ P → ∀ m : M, m ∈ P

/-- Noetherianity of the actual unitized module is finite stable generation
of every original stable additive subgroup. -/
def NoetherianGenerationStatement : Prop :=
  ∀ (A : Type uA) (M : Type uM)
    [NonUnitalRing A] [AddCommGroup M] [NonUnitalModule A M],
    (letI := CompatibleUnitization.module
      (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
      IsNoetherian (Unitization ℤ A) M) ↔
    ∀ P : NonUnitalSubmodule A M,
      ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
        ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q

/-- The submodule, whole-module and Noetherian comparisons, in that order. -/
def IntegerOriginalSubmoduleGenerationStatement : Prop :=
  SubmoduleGenerationStatement.{uA, uM} ∧
    ModuleGenerationStatement.{uA, uM} ∧
    NoetherianGenerationStatement.{uA, uM}

end Langlands.Algebra.IntegerOriginalSubmoduleGeneration
