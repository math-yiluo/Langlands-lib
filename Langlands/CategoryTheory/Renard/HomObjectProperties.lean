import Langlands.CategoryTheory.Renard.HomFunctors
import Langlands.CategoryTheory.RenardExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Renard's Hom definitions of projective and generator objects

These are the five object properties defined in Renard A.VIII.2.
Exactness is the published source sequence condition on the actual
integer-module-valued Hom functor; faithfulness is Mathlib functor faithfulness.
-/

open CategoryTheory

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard projectivity: the actual covariant Hom functor is sequence exact. -/
def HomProjective (P : C) : Prop :=
  SequenceExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

/-- Renard injectivity: the actual Hom functor on `Cᵒᵖ` is sequence exact. -/
def HomInjective (P : C) : Prop :=
  ContravariantSequenceExact (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P)

/-- Renard generation: the actual covariant Hom functor is faithful. -/
def HomGenerator (P : C) : Prop :=
  (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful

/-- Renard cogeneration: the actual contravariant Hom functor is faithful. -/
def HomCogenerator (P : C) : Prop :=
  (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P).Faithful

/-- Renard's progenerator is a projective generator. -/
def HomProgenerator (P : C) : Prop :=
  HomProjective P ∧ HomGenerator P

/-- Definitional unfolding of Renard projectivity. -/
theorem homProjective_iff (P : C) :
    HomProjective P ↔
      SequenceExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P) :=
  Iff.rfl

/-- Definitional unfolding of Renard injectivity. -/
theorem homInjective_iff (P : C) :
    HomInjective P ↔
      ContravariantSequenceExact (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P) :=
  Iff.rfl

/-- Definitional unfolding of Renard generation. -/
theorem homGenerator_iff (P : C) :
    HomGenerator P ↔
      (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful :=
  Iff.rfl

/-- Definitional unfolding of Renard cogeneration. -/
theorem homCogenerator_iff (P : C) :
    HomCogenerator P ↔
      (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P).Faithful :=
  Iff.rfl

/-- Definitional unfolding of Renard's projective generator condition. -/
theorem homProgenerator_iff (P : C) :
    HomProgenerator P ↔ HomProjective P ∧ HomGenerator P :=
  Iff.rfl

end Langlands.Renard
