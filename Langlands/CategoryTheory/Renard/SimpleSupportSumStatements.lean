import Langlands.CategoryTheory.Renard.SimpleSupportSum
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Renard A.IX: support and maximality of the supported sum

These are proposition targets for the source assertion that the actual sum
`E_S` is supported on `S`, and for its resulting greatest-element property.
The source Grothendieck hypothesis has an independent family size `w`. The
family of supported subobjects of `X` is assumed `w`-small, so the coproduct
used by the actual sum comes from the source hypothesis. Coproducts of size
`max u v` cannot be assumed instead: they force every Hom type to be a
subsingleton. No assertion is proved in this statement unit.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe w u v

noncomputable section

/-- Renard A.IX, printed page 268 / PDF274: the actual sum `E_S` belongs to
the supported full subcategory `M_S`. -/
@[pp_with_univ]
def SimpleSupportSumSupportStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    SourceAB6 C → ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (X : C) [Small.{w} (simpleSupportSubobjects S X)],
        letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
          hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
        HasSimpleSupport S (simpleSupportSum S X : C)

/-- Internal consequence target: membership of `E_S` together with the public
upper-bound law makes it the greatest actual supported subobject. -/
@[pp_with_univ]
def SimpleSupportSumMaximumStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    SourceAB6 C → ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (X : C) [Small.{w} (simpleSupportSubobjects S X)],
        letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
          hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
        IsGreatest (simpleSupportSubobjects S X) (simpleSupportSum S X)

/-- The source support assertion and its internal maximality consequence,
with the complete source setting retained in each component. -/
@[pp_with_univ]
def SimpleSupportSumStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSupportSumSupportStatement.{w} C ∧ SimpleSupportSumMaximumStatement.{w} C

end

end Langlands.Renard
