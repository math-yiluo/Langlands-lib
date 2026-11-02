import Langlands.CategoryTheory.Renard.SimpleSupportSumStatements
import Langlands.CategoryTheory.Renard.SimpleSupportOrthogonalityStatements

/-!
# Renard A.IX: disjointness of the actual full supported sums

This proposition target specializes the source's zero-intersection and
binary direct-sum inclusion assertions to `simpleSupportSum S X` and
`simpleSupportSum T X`. Both full supported-subobject families must be
small at the independent source coproduct size. This statement unit
contains no proof of the target.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

/-- Renard A.IX, printed page 268 / PDF274: for disjoint subsets of the
simple classes, the actual full supported sums have zero intersection,
and their actual canonical binary-biproduct map into `X` is monic.
The two family-size premises supply the coproducts used by those sums. -/
@[pp_with_univ]
def SimpleSupportSumOrthogonalityStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    SourceAB6 C →
      ∀ S T : Set (ObjectClass C), S ⊆ simpleClasses C →
        T ⊆ simpleClasses C → Disjoint S T →
          ∀ (X : C) [Small.{w} (simpleSupportSubobjects S X)]
            [Small.{w} (simpleSupportSubobjects T X)],
            letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
              hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
            letI : HasCoproductsOfShape (simpleSupportSubobjects T X) C :=
              hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects T X)
            simpleSupportSum S X ⊓ simpleSupportSum T X = ⊥ ∧
              Mono (biprod.desc (simpleSupportSum S X).arrow
                (simpleSupportSum T X).arrow)

end

end Langlands.Renard
