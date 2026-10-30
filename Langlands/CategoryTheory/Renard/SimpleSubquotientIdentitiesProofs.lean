import Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient
import Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty
import Langlands.CategoryTheory.Renard.SimpleSubquotientSum

/-!
# Renard A.VI.3: all three simple-subquotient identities

Packages the published proofs of clauses (i), (ii) and (iii) of the
unnumbered Lemma on printed page 264 / PDF270 of the 9 July 2026 French
edition into the aggregate conjunction, in source order.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- Renard A.VI.3, unnumbered Lemma (i)–(iii), with the original source
antecedents retained in each clause. -/
theorem simpleSubquotientIdentities
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSubquotientIdentitiesStatement.{w} C :=
  ⟨simpleSubquotientSubobjectQuotient.{w} C, simpleSubquotientEmpty.{w} C,
    simpleSubquotientSum.{w} C⟩

end Langlands.Renard
