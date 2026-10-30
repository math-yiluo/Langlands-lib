import Langlands.CategoryTheory.Renard.SimpleSupport
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Renard A.IX: colimits of supported objects

Proposition targets for the colimit-closure assertion on printed268/PDF274
of the French edition dated 9 July 2026. The source family universe is
retained. General colimits are expressed using actual cocones and their
universal properties, with an independent diagram Hom universe.
-/

universe w t v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- The actual `w`-indexed coproduct of supported objects is supported.
The coproduct instance is supplied by the original source hypothesis. -/
@[pp_with_univ]
def SimpleSupportCoproductStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C, SourceAB6 C →
    letI : HasCoproducts.{w} C := hG.1
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (I : Type w) (F : I → C),
        (∀ i, HasSimpleSupport S (F i)) →
          HasSimpleSupport S (∐ F)

/-- Every actual colimit cocone of a diagram of supported objects with
object index in `Type w` has a supported vertex. No global colimit-existence premise
or relation between the diagram Hom and object universes is added. -/
@[pp_with_univ]
def SimpleSupportColimitStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (J : Type w) [Category.{t} J] (F : J ⥤ C) (c : Cocone F),
        IsColimit c → (∀ j, HasSimpleSupport S (F.obj j)) →
          HasSimpleSupport S c.pt

/-- The source colimit-closure assertion with an explicit coproduct
component for reuse in its proof. -/
@[pp_with_univ]
def SimpleSupportColimitClosureStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSupportCoproductStatement.{w} C ∧
    SimpleSupportColimitStatement.{w,t} C

end Langlands.Renard
