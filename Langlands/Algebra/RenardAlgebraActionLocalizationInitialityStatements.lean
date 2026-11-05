import Langlands.Algebra.RenardAlgebraActionLocalizationCategory

/-!
# Initiality of the canonical arrow of the localized algebra action

Statements for the categorical form of the last sentence of Renard A.III.1, example 5
(9 July 2026, printed p. 252 / PDF p. 258): the canonical structured arrow of the
localized B-module solves the right universal problem for the inclusion of the pairs
with invertible endomorphism.
-/

set_option autoImplicit false

universe u v w x

open CategoryTheory

namespace Langlands.Renard.AlgebraActionLocalization

/-- Every morphism from the raised pair to a pair with invertible endomorphism factors
uniquely through the canonical arrow. -/
def FactorizationStatement : Prop :=
  ∀ (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B] [Module k B]
    (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T),
    ∃! h : localizedObject.{u, v, w, x} A ⟶ T,
      canonicalArrow.{u, v, w, x} A ≫
        (invertibleActionInclusion.{u, v, max u w x} k B).map h = g

/-- The canonical structured arrow admits initiality data.
`Nonempty` makes this a proposition, rather than a choice of that data. -/
def InitialityStatement : Prop :=
  ∀ (k : Type u) [CommRing k] (B : Type v) [NonUnitalRing B] [Module k B]
    (A : ActionEndomorphismCat.{u, v, w} k B),
    Nonempty (StructuredArrow.IsUniversal (canonicalStructuredArrow.{u, v, w, x} A))

/-- The factorization over an arbitrary field, for a nonunital algebra with the complete
bilinear interface, with no dimension restriction. -/
def FieldFactorizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (B : Type v) [NonUnitalRing B] [Module k B]
    [IsScalarTower k B B] [SMulCommClass k B B]
    (A : ActionEndomorphismCat.{u, v, w} k B)
    (T : InvertibleActionEndomorphismCat.{u, v, max u w x} k B)
    (g : (raisedFunctor.{u, v, w, x} k B).obj A ⟶
      (invertibleActionInclusion.{u, v, max u w x} k B).obj T),
    ∃! h : localizedObject.{u, v, w, x} A ⟶ T,
      canonicalArrow.{u, v, w, x} A ≫
        (invertibleActionInclusion.{u, v, max u w x} k B).map h = g

/-- Closed factorization, initiality and field assertions for the canonical arrow into
the full subcategory of pairs with invertible endomorphism. -/
def InitialityStatements : Prop :=
  FactorizationStatement.{u, v, w, x} ∧
    InitialityStatement.{u, v, w, x} ∧
    FieldFactorizationStatement.{u, v, w, x}

end Langlands.Renard.AlgebraActionLocalization
