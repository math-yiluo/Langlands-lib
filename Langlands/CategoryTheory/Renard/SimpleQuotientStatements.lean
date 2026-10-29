import Langlands.CategoryTheory.Renard.CompositionChains
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Langlands.CategoryTheory.RenardGrothendieckAxioms

/-!
# Renard A.VI.3: simple quotients and simple subquotients

The two clauses of the unnumbered Proposition on printed page 264 / PDF270
of the 9 July 2026 French edition. These are proposition targets only.
The common source Grothendieck and AB6 assumptions remain explicit.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- In the source context, a nonzero finite-type object has a simple
quotient, realized as the actual cokernel of a proper subobject arrow. -/
@[pp_with_univ]
def FiniteTypeSimpleQuotientStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ X : C, ¬ IsZero X → Langlands.Renard.IsFiniteTypeObject X →
      ∃ P : Subobject X, P < ⊤ ∧ Simple (cokernel P.arrow)

/-- In the source context, an object that is not of finite type has a
simple actual quotient of two strictly nested subobjects. -/
@[pp_with_univ]
def NonFiniteTypeSimpleSubquotientStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ X : C, ¬ Langlands.Renard.IsFiniteTypeObject X →
      ∃ (A B : Subobject X) (h : A < B),
        Simple (cokernel (Subobject.ofLE A B h.le))

/-- Both clauses of Renard A.VI.3's simple-quotient Proposition. -/
@[pp_with_univ]
def SimpleQuotientPropositionStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  FiniteTypeSimpleQuotientStatement.{w} C ∧
    NonFiniteTypeSimpleSubquotientStatement.{w} C

end Langlands.Renard
