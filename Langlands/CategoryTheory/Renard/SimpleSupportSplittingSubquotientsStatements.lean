import Langlands.CategoryTheory.Renard.SimpleSupportSplitting
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Renard A.IX: a support partition splits every subquotient of a split object

Proposition target for the unnumbered lemma on printed268/PDF274 of the
French edition dated 9 July 2026. A subquotient is presented by an actual
monomorphism into the original object and an actual epimorphism to the
subquotient. Both splitting predicates use the actual public supported sums
and their canonical inclusion maps.

The source family universe `r`, partition universe `w`, Hom universe `v`
and object universe `u` remain independent. The smallness conditions make
explicit exactly the source-sized partition and the full supported-subobject
families at the two endpoints. No splitting theorem is proved here.
-/

universe r w v u

open CategoryTheory

namespace Langlands.Renard

/-- Renard A.IX, printed268/PDF274: every actual subquotient of an object
split by a support partition is split by the same partition. -/
@[pp_with_univ]
def SimpleSupportPartitionSubquotientStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{r} C → SourceAB6 C →
    ∀ (I : Type w) [Small.{r} I] (S : I → Set (ObjectClass C)),
      ∀ (X : C) [∀ i : I, Small.{r} (simpleSupportSubobjects (S i) X)],
        SimpleSupportPartitionSplits S X →
          ∀ (N Y : C) (j : N ⟶ X) (p : N ⟶ Y) [Mono j] [Epi p]
            [∀ i : I, Small.{r} (simpleSupportSubobjects (S i) Y)],
            SimpleSupportPartitionSplits S Y

end Langlands.Renard
