import Langlands.CategoryTheory.RenardSemisimplicity
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Mathlib.Logic.Small.Basic

/-!
# Renard A.VII: the semisimplicity equivalence

Source: Renard, French edition dated 9 July 2026, Appendix A.VII,
printed page 265 / PDF page 271, with the hypotheses on printed page 263.

The source-family universe `r`, Hom universe `v` and object universe `u`
are independent. Smallness of the actual subobject type at the object in
question makes the source's set-indexed proof available at size `r`.
The first conjunct states the internal comparison between the existing
semisimple-object alias and source-sized complete reducibility.
This file states the equivalences and proves none of them.
-/

universe r v u

open CategoryTheory

namespace Langlands.Renard

/-- Renard A.VII's three conditions, using the actual semisimple-object
alias, together with its comparison to complete reducibility at the source
size. The source hypotheses and the object's subobject-size presupposition
are quantified within the proposition. -/
@[pp_with_univ]
def SemisimplicityEquivalenceStatement (C : Type u)
    [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{r} C → SourceAB6 C →
    ∀ (X : C) [Small.{r} (Subobject X)],
      (IsSemisimpleObject X ↔ IsCompletelyReducible.{r} X) ∧
      (IsSemisimpleObject X ↔ IsSumOfSimpleSubobjects X) ∧
      (IsSumOfSimpleSubobjects X ↔ EverySubobjectHasComplement X)

end Langlands.Renard
