import Langlands.CategoryTheory.RenardSemisimplicity
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Mathlib.Logic.Small.Basic

/-!
# Renard A.VII: subobjects of semisimple objects

Source: Renard, French edition dated 9 July 2026, Appendix A.VII,
unnumbered corollary, printed page 265 / PDF page 271.

The source-family universe `r`, Hom universe `v` and object universe `u`
are independent. The full subobject type of the ambient object is explicitly
small at the source size. An arbitrary monomorphism represents the subobject.
This file states the corollary and supplies no proof of it.
-/

universe r v u

open CategoryTheory

namespace Langlands.Renard

/-- Under Renard's source Grothendieck and local-finite-type hypotheses,
every object embedding into a semisimple object is semisimple. Only the
ambient object's full subobject type is required to be source-small. -/
@[pp_with_univ]
def SemisimpleSubobjectStatement (C : Type u)
    [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{r} C → SourceAB6 C →
    ∀ (X : C) [Small.{r} (Subobject X)],
      IsSemisimpleObject X →
        ∀ (Y : C) (j : Y ⟶ X) [Mono j], IsSemisimpleObject Y

end Langlands.Renard
