import Langlands.CategoryTheory.Renard.CompositionChains
import Langlands.CategoryTheory.Renard.IndexedSubobjectSums
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Langlands.CategoryTheory.RenardGrothendieckAxioms

/-!
# Renard A.VI.3: identities for simple-subquotient classes

The three clauses of the unnumbered Lemma on printed page 264 / PDF270
of the 9 July 2026 French edition. These are proposition targets only.
The source Grothendieck and canonical AB6 assumptions are retained in
each component, with independent family, Hom and object universes.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- In the source context, simple-subquotient classes of an object are
the union of those of a subobject and its actual cokernel quotient. -/
@[pp_with_univ]
def SimpleSubquotientSubobjectQuotientStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ (X : C) (P : Subobject X),
      simpleSubquotientClasses X =
        simpleSubquotientClasses (P : C) ∪
          simpleSubquotientClasses (cokernel P.arrow)

/-- In the source context, an object has no simple-subquotient class
exactly when it is a categorical zero object. -/
@[pp_with_univ]
def SimpleSubquotientEmptyStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ X : C, simpleSubquotientClasses X = ∅ ↔ IsZero X

/-- In the source context, simple-subquotient classes of an arbitrary
indexed subobject sum form the union of those of its summands. The
coproduct instance is obtained inside the proposition from `hG`. -/
@[pp_with_univ]
def SimpleSubquotientSumStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C, SourceAB6 C →
    letI : HasCoproducts.{w} C := hG.1
    ∀ (X : C) (I : Type w) (F : I → Subobject X),
      simpleSubquotientClasses (subobjectSum F : C) =
        ⋃ i, simpleSubquotientClasses (F i : C)

/-- All three clauses of Renard A.VI.3's simple-subquotient Lemma. -/
@[pp_with_univ]
def SimpleSubquotientIdentitiesStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSubquotientSubobjectQuotientStatement.{w} C ∧
    SimpleSubquotientEmptyStatement.{w} C ∧
      SimpleSubquotientSumStatement.{w} C

end Langlands.Renard
