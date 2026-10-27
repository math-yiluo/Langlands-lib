import Mathlib.Algebra.Algebra.Unitization
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Explicit regular-action and left-ideal Noetherian criteria

Derived internal statement targets. The additive and scalar-linear
left-ideal conventions are written out separately.
-/

set_option autoImplicit false

namespace Langlands.Algebra.UnitizationIdealNoetherian

universe uR uA

/-- The regular-module form of the Noetherian unitization criterion. -/
def RegularCriterionStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA)
    [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module (Unitization R A) A],
    (∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) →
    (IsNoetherianRing (Unitization R A) ↔
      IsNoetherianRing R ∧ IsNoetherian (Unitization R A) A)

/-- Over Noetherian scalars, use all scalar-linear left ideals and their
explicit stable-generation property. -/
def ScalarIdealCriterionStatement : Prop :=
  ∀ (R : Type uR) (A : Type uA)
    [CommRing R] [IsNoetherianRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    [Module (Unitization R A) A] [IsScalarTower R (Unitization R A) A],
    (∀ (u : Unitization R A) (a : A),
      u • a = u.fst • a + u.snd * a) →
    (IsNoetherianRing (Unitization R A) ↔
      ∀ P : Submodule R A,
        (∀ (a x : A), x ∈ P → a * x ∈ P) →
        ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
          ∀ Q : Submodule R A,
            (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
            (↑S : Set A) ⊆ Q → P ≤ Q)

/-- Integer unitization uses all additive left ideals, without a scalar
linearity restriction. -/
def AdditiveIdealCriterionStatement : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module (Unitization ℤ A) A],
    (∀ (u : Unitization ℤ A) (a : A),
      u • a = u.fst • a + u.snd * a) →
    (IsNoetherianRing (Unitization ℤ A) ↔
      ∀ P : AddSubgroup A,
        (∀ (a x : A), x ∈ P → a * x ∈ P) →
        ∃ S : Finset A, (↑S : Set A) ⊆ P ∧
          ∀ Q : AddSubgroup A,
            (∀ (a x : A), x ∈ Q → a * x ∈ Q) →
            (↑S : Set A) ⊆ Q → P ≤ Q)

/-- The regular criterion and the two explicit left-ideal criteria. -/
def UnitizationIdealNoetherianStatement : Prop :=
  RegularCriterionStatement.{uR, uA} ∧
    ScalarIdealCriterionStatement.{uR, uA} ∧
    AdditiveIdealCriterionStatement.{uA}

end Langlands.Algebra.UnitizationIdealNoetherian
