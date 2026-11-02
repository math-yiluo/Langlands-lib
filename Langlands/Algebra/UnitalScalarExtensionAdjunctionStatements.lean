import Langlands.Algebra.UnitalScalarExtension
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard A.V.2: scalar extension and restriction are adjoint

These are proposition definitions over the published balanced quotient and
the actual scalar-extension and restriction functors.
-/

set_option autoImplicit false

open CategoryTheory
open Langlands.Algebra.UnitalScalarExtension

namespace Langlands.Algebra.UnitalScalarExtensionAdjunction

universe uB uA uM

variable {B : Type uB} {A : Type uA} [Ring B] [Ring A] (φ : B →+* A)

/-- The source's theta and sigma are the two maps of this native Hom equivalence. -/
def HomFormulas (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (f : (functor.{uB, uA, uM} φ).obj X ⟶ Y) (x : X),
    (adj.homEquiv X Y f).hom x = f.hom (tmul φ X 1 x)) ∧
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (g : X ⟶ (restriction.{uB, uA, max uA uM} φ).obj Y) (a : A) (x : X),
    ((adj.homEquiv X Y).symm g).hom (tmul φ X a x) = a • g.hom x)

/-- Both inverse identities hold as equalities of whole module morphisms. -/
def HomInverseLaws (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (f : (functor.{uB, uA, uM} φ).obj X ⟶ Y),
    (adj.homEquiv X Y).symm (adj.homEquiv X Y f) = f) ∧
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (g : X ⟶ (restriction.{uB, uA, max uA uM} φ).obj Y),
    adj.homEquiv X Y ((adj.homEquiv X Y).symm g) = g)

/-- Joint naturality under precomposition in X and postcomposition in Y. -/
def HomNaturality (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X' X : ModuleCat.{max uA uM} B) (Y Y' : ModuleCat.{max uA uM} A)
    (u : X' ⟶ X) (v : Y ⟶ Y') (f : (functor.{uB, uA, uM} φ).obj X ⟶ Y),
    adj.homEquiv X' Y' ((functor.{uB, uA, uM} φ).map u ≫ f ≫ v) =
      u ≫ adj.homEquiv X Y f ≫ (restriction.{uB, uA, max uA uM} φ).map v) ∧
  (∀ (X' X : ModuleCat.{max uA uM} B) (Y Y' : ModuleCat.{max uA uM} A)
    (u : X' ⟶ X) (v : Y ⟶ Y') (g : X ⟶ (restriction.{uB, uA, max uA uM} φ).obj Y),
    (adj.homEquiv X' Y').symm (u ≫ g ≫ (restriction.{uB, uA, max uA uM} φ).map v) =
      (functor.{uB, uA, uM} φ).map u ≫ (adj.homEquiv X Y).symm g ≫ v)

/-- The unit and counit of the same adjunction have the source's exact values. -/
def UnitCounitFormulas (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X : ModuleCat.{max uA uM} B) (x : X),
    (adj.unit.app X).hom x = tmul φ X 1 x) ∧
  (∀ (Y : ModuleCat.{max uA uM} A) (a : A) (y : Y),
    (adj.counit.app Y).hom (tmul φ ((restriction.{uB, uA, max uA uM} φ).obj Y) a y) = a • y)

/-- The unit and counit are natural for the actual extension and restriction maps. -/
def UnitCounitNaturality (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X X' : ModuleCat.{max uA uM} B) (u : X ⟶ X'),
    u ≫ adj.unit.app X' = adj.unit.app X ≫ (restriction.{uB, uA, max uA uM} φ).map ((functor.{uB, uA, uM} φ).map u)) ∧
  (∀ (Y Y' : ModuleCat.{max uA uM} A) (v : Y ⟶ Y'),
    (functor.{uB, uA, uM} φ).map ((restriction.{uB, uA, max uA uM} φ).map v) ≫ adj.counit.app Y' = adj.counit.app Y ≫ v)

/-- Both component triangle equations, with no tensor object supplied as input. -/
def TriangleIdentities (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X : ModuleCat.{max uA uM} B),
    (functor.{uB, uA, uM} φ).map (adj.unit.app X) ≫ adj.counit.app ((functor.{uB, uA, uM} φ).obj X) = 𝟙 ((functor.{uB, uA, uM} φ).obj X)) ∧
  (∀ (Y : ModuleCat.{max uA uM} A),
    adj.unit.app ((restriction.{uB, uA, max uA uM} φ).obj Y) ≫ (restriction.{uB, uA, max uA uM} φ).map (adj.counit.app Y) = 𝟙 ((restriction.{uB, uA, max uA uM} φ).obj Y))

/-- The Hom maps agree with those reconstructed from this unit and counit. -/
def HomUnitCounitRelations (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (f : (functor.{uB, uA, uM} φ).obj X ⟶ Y),
    adj.homEquiv X Y f = adj.unit.app X ≫ (restriction.{uB, uA, max uA uM} φ).map f) ∧
  (∀ (X : ModuleCat.{max uA uM} B) (Y : ModuleCat.{max uA uM} A)
    (g : X ⟶ (restriction.{uB, uA, max uA uM} φ).obj Y),
    (adj.homEquiv X Y).symm g = (functor.{uB, uA, uM} φ).map g ≫ adj.counit.app Y)

/-- All explicit source formulas and adjunction laws for one chosen adjunction. -/
def AdjunctionProperties (adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ) : Prop :=
  HomFormulas φ adj ∧
    HomInverseLaws φ adj ∧
    HomNaturality φ adj ∧
    UnitCounitFormulas φ adj ∧
    UnitCounitNaturality φ adj ∧
    TriangleIdentities φ adj ∧
    HomUnitCounitRelations φ adj

/-- Closed scalar-adjunction target over arbitrary possibly noncommutative rings. -/
def ScalarExtensionAdjunctionStatements : Prop :=
  ∀ (B : Type uB) (A : Type uA) [Ring B] [Ring A] (φ : B →+* A),
    ∃ adj : functor.{uB, uA, uM} φ ⊣ restriction.{uB, uA, max uA uM} φ,
      AdjunctionProperties φ adj

end Langlands.Algebra.UnitalScalarExtensionAdjunction
