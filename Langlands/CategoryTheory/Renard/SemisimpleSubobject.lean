import Langlands.CategoryTheory.Renard.SemisimpleSubobjectStatements
import Langlands.CategoryTheory.Renard.SemisimplicityEquivalence

/-!
# Renard A.VII: subobjects of semisimple objects are semisimple

Proof of `Langlands.Renard.SemisimpleSubobjectStatement` (Renard, French
edition dated 9 July 2026, Appendix A.VII, unnumbered corollary, printed page
265 / PDF page 271). By the A.VII equivalence, a semisimple object with
source-small subobjects has a complemented subobject lattice. Complements
pass to the subobject represented by a monomorphism `j : Y ⟶ X` by the
modular law, and the subobjects of `Y` inherit source smallness, so the
equivalence applies again to `Y`.
-/

universe r v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- A monomorphism into an object with source-small subobjects has
source-small subobjects. -/
theorem small_subobject_of_mono {C : Type u} [Category.{v} C] {X Y : C} (j : Y ⟶ X)
    [Mono j] [Small.{r} (Subobject X)] : Small.{r} (Subobject Y) :=
  small_of_injective (Subobject.map_obj_injective j)

section Transport

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Complementedness of the subobject lattice passes along a monomorphism
`j : Y ⟶ X`: the subobjects of `Y` are those of the object underlying
`Subobject.mk j`. -/
theorem complementedLattice_subobject_of_mono {X Y : C} (j : Y ⟶ X) [Mono j]
    [ComplementedLattice (Subobject X)] : ComplementedLattice (Subobject Y) :=
  have := complementedLattice_subobject (Subobject.mk j)
  (Subobject.mapIsoToOrderIso (Subobject.underlyingIso j)).complementedLattice

/-- Every subobject of `Y` has a canonical complement if every subobject of
`X` has one, for a monomorphism `j : Y ⟶ X`. -/
theorem everySubobjectHasComplement_of_mono {X Y : C} (j : Y ⟶ X) [Mono j]
    (h : EverySubobjectHasComplement X) : EverySubobjectHasComplement Y := by
  have := (everySubobjectComplementedLattice C X).mp h
  have := complementedLattice_subobject_of_mono j
  exact (everySubobjectComplementedLattice C Y).mpr this

end Transport

/-- Renard A.VII, corollary: under the source hypotheses, every object
embedding into a semisimple object whose subobject type is `r`-small is
semisimple. -/
theorem semisimpleSubobject (C : Type u) [Category.{v} C] [Abelian C] :
    SemisimpleSubobjectStatement.{r} C := by
  intro hG hAB6 X _ hX Y j _
  have hE := semisimplicityEquivalence.{r} C hG hAB6
  have : Small.{r} (Subobject Y) := small_subobject_of_mono j
  have hXc : EverySubobjectHasComplement X := (hE X).2.2.mp ((hE X).2.1.mp hX)
  exact (hE Y).2.1.mpr ((hE Y).2.2.mpr (everySubobjectHasComplement_of_mono j hXc))

end Langlands.Renard
