import Langlands.CategoryTheory.Renard.FixedDimensionVectorSpaces

/-!
# Renard A.II.2: the fixed-dimension vector-space equivalence

The actual inclusion of the one-object coordinate category admits one
reverse functor and both actual natural isomorphisms.
-/

open CategoryTheory

namespace Langlands.Renard

/-- The fixed-dimension vector-space example in Renard A.II.2,
printed p.251 / PDF257, with the correctly typed identity functors. -/
@[pp_with_univ]
def FixedDimensionVectorSpaceEquivalenceStatement.{u, v}
    (k : Type u) [Field k] (n : ℕ) : Prop :=
  ∃ G : FixedDimensionVectorSpaces.{u, v} k n ⥤
      OneObjectVectorSpaceCategory.{u, v} k n,
    Nonempty (fixedDimensionVectorSpaceInclusion.{u, v} k n ⋙ G ≅
      𝟭 (OneObjectVectorSpaceCategory.{u, v} k n)) ∧
    Nonempty (G ⋙ fixedDimensionVectorSpaceInclusion.{u, v} k n ≅
      𝟭 (FixedDimensionVectorSpaces.{u, v} k n))

end Langlands.Renard
