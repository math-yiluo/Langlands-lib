import Langlands.Algebra.RenardEndomorphismLocalizationComparison

/-! # Initiality of the explicit and chosen endomorphism-localization arrows -/

set_option autoImplicit false

universe u v w

open CategoryTheory Langlands.Algebra.PolynomialEndomorphism

namespace Langlands.Renard.EndomorphismLocalization.ChosenComparison

/-- Every intertwiner from the raised pair to an invertible pair factors uniquely
through the explicit canonical arrow iota. -/
def ExplicitFactorizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : EndomorphismCat.{u, v} R)
    (B : InvertibleEndomorphismCat.{u, max u v w} R)
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B),
    ∃! h : (explicitFunctor.{u, v, w} R).obj A ⟶ B,
      (explicitArrow.{u, v, w} R).app A ≫
        (invertibleEndomorphismInclusion.{u, max u v w} R).map h = g

/-- Every intertwiner from the raised pair to an invertible pair factors uniquely
through the chosen canonical arrow lambda. -/
def ChosenFactorizationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : EndomorphismCat.{u, v} R)
    (B : InvertibleEndomorphismCat.{u, max u v w} R)
    (g : (raisedFunctor.{u, v, w} R).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} R).obj B),
    ∃! h : (chosenFunctor.{u, v, w} R).obj A ⟶ B,
      (chosenArrow.{u, v, w} R).app A ≫
        (invertibleEndomorphismInclusion.{u, max u v w} R).map h = g

/-- The explicit structured arrow admits initiality data.
`Nonempty` makes this a proposition, rather than a choice of that data. -/
def ExplicitInitialityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : EndomorphismCat.{u, v} R),
    Nonempty (StructuredArrow.IsUniversal (explicitStructuredArrow.{u, v, w} R A))

/-- The chosen structured arrow admits initiality data. -/
def ChosenInitialityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : EndomorphismCat.{u, v} R),
    Nonempty (StructuredArrow.IsUniversal (chosenStructuredArrow.{u, v, w} R A))

/-- The components of alpha and its inverse are the only morphisms of invertible
pairs carrying either canonical arrow to the other. -/
def ComparisonUniquenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (A : EndomorphismCat.{u, v} R),
    (∀ h : (chosenFunctor.{u, v, w} R).obj A ⟶ (explicitFunctor.{u, v, w} R).obj A,
      (chosenArrow.{u, v, w} R).app A ≫
          (invertibleEndomorphismInclusion.{u, max u v w} R).map h =
        (explicitArrow.{u, v, w} R).app A →
      h = (targetComparison.{u, v, w} R).hom.app A) ∧
    (∀ h : (explicitFunctor.{u, v, w} R).obj A ⟶ (chosenFunctor.{u, v, w} R).obj A,
      (explicitArrow.{u, v, w} R).app A ≫
          (invertibleEndomorphismInclusion.{u, max u v w} R).map h =
        (chosenArrow.{u, v, w} R).app A →
      h = (targetComparison.{u, v, w} R).inv.app A)

/-- The explicit factorization over an arbitrary field, with no dimension restriction. -/
def FieldExplicitFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (A : EndomorphismCat.{u, v} k)
    (B : InvertibleEndomorphismCat.{u, max u v w} k)
    (g : (raisedFunctor.{u, v, w} k).obj A ⟶
      (invertibleEndomorphismInclusion.{u, max u v w} k).obj B),
    ∃! h : (explicitFunctor.{u, v, w} k).obj A ⟶ B,
      (explicitArrow.{u, v, w} k).app A ≫
        (invertibleEndomorphismInclusion.{u, max u v w} k).map h = g

/-- Closed factorization, initiality and comparison-uniqueness assertions for the
two actual canonical arrows into the full subcategory of invertible pairs. -/
def InitialityStatements : Prop :=
  ExplicitFactorizationStatement.{u, v, w} ∧
    ChosenFactorizationStatement.{u, v, w} ∧
    ExplicitInitialityStatement.{u, v, w} ∧
    ChosenInitialityStatement.{u, v, w} ∧
    ComparisonUniquenessStatement.{u, v, w} ∧
    FieldExplicitFactorizationStatement.{u, v, w}

end Langlands.Renard.EndomorphismLocalization.ChosenComparison
