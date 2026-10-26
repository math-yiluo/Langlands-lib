import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Renard's AB4, AB4*, AB5 and Grothendieck-category conventions

Source: Renard (9 July 2026), Appendix A.VI.2, printed page 263.
Families are indexed by types in the universe `w`, independent of the object
universe `u` and the Hom universe `v`. All sums of subobjects are least upper
bounds in the existing order on categorical subobjects.

These are Renard's existence conventions. They differ from Mathlib's
`AB4OfSize`, `AB4StarOfSize`, `AB5OfSize` and `IsGrothendieckAbelian`.
-/

universe w v u

open CategoryTheory Limits

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C]

/-- Renard's AB4 at size `w`: every `w`-indexed family of objects has a product.
No exactness is asserted. -/
@[pp_with_univ]
abbrev SourceAB4 : Prop :=
  HasProducts.{w} C

/-- Renard's AB4* at size `w`: every `w`-indexed family of objects has a
coproduct (direct sum). No exactness is asserted. -/
@[pp_with_univ]
abbrev SourceAB4Star : Prop :=
  HasCoproducts.{w} C

/-- Renard's complete abelian category at size `w`: an abelian category
satisfying the source AB4. -/
@[pp_with_univ]
abbrev IsSourceComplete [Abelian C] : Prop :=
  SourceAB4.{w} C

/-- Renard's cocomplete abelian category at size `w`: an abelian category
satisfying the source AB4*. -/
@[pp_with_univ]
abbrev IsSourceCocomplete [Abelian C] : Prop :=
  SourceAB4Star.{w} C

/-- Intersection distributes over sums of nonempty directed `w`-indexed families
of subobjects: the sum of the family exists, and its intersection with any
subobject `N` is the sum of the intersections with `N`. -/
@[pp_with_univ]
def DirectedSubobjectSumsDistribute [Abelian C] : Prop :=
  ∀ (X : C) (I : Type w), Nonempty I →
    ∀ F : I → Subobject X, Directed (· ≤ ·) F →
      ∀ N : Subobject X, ∃ U : Subobject X,
        IsLUB (Set.range F) U ∧ IsLUB (Set.range fun i => N ⊓ F i) (N ⊓ U)

/-- Renard's AB5 at size `w`: the abelian category is cocomplete, and
intersection distributes over sums of filtered increasing systems of
subobjects. -/
@[pp_with_univ]
def SourceAB5 [Abelian C] : Prop :=
  IsSourceCocomplete.{w} C ∧ DirectedSubobjectSumsDistribute.{w} C

/-- Renard's Grothendieck category at size `w`: a cocomplete abelian category
satisfying AB5. Cocompleteness is the first conjunct of `SourceAB5`. There is
no generator or separator clause. -/
@[pp_with_univ]
def IsSourceGrothendieck [Abelian C] : Prop :=
  SourceAB5.{w} C

/-- Comparison condition: every `w`-indexed family of subobjects of every
object, including the empty family, has a least upper bound. -/
@[pp_with_univ]
def HasIndexedSubobjectSums : Prop :=
  ∀ (X : C) (I : Type w) (F : I → Subobject X),
    ∃ U : Subobject X, IsLUB (Set.range F) U

end Langlands.Renard
