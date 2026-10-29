import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Renard's Hom left exactness and comparisons with lifting classes

The first two propositions state the Hom left-exactness assertions in
Renard A.VIII.2. The next two are derived comparisons of his exact-Hom
definitions with Mathlib's projective and injective lifting classes.
-/

open CategoryTheory

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual covariant integer-module Hom functor is left sequence exact. -/
def CovariantHomLeftExactStatement (P : C) : Prop :=
  SequenceLeftExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

/-- The actual contravariant Hom functor is left sequence exact on `Cᵒᵖ`. -/
def ContravariantHomLeftExactStatement (P : C) : Prop :=
  ContravariantSequenceLeftExact (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P)

/-- Compare Renard's exact-Hom projectivity with Mathlib's lifting class. -/
def HomProjectiveComparisonStatement (P : C) : Prop :=
  HomProjective P ↔ CategoryTheory.Projective P

/-- Compare Renard's exact-Hom injectivity with Mathlib's extension class. -/
def HomInjectiveComparisonStatement (P : C) : Prop :=
  HomInjective P ↔ CategoryTheory.Injective P

/-- The two Hom left-exactness assertions and the two derived comparisons. -/
def HomExactnessComparisonStatement (P : C) : Prop :=
  CovariantHomLeftExactStatement P ∧
    ContravariantHomLeftExactStatement P ∧
    HomProjectiveComparisonStatement P ∧
    HomInjectiveComparisonStatement P

end Langlands.Renard
