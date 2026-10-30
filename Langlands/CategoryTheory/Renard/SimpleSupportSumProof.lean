import Langlands.CategoryTheory.Renard.SimpleSupportSumStatements
import Langlands.CategoryTheory.Renard.SimpleSubquotientSum

/-!
# Support and maximality of Renard's actual supported-subobject sum

Renard A.IX, printed page 268 / PDF274. Reindex the full supported family
by `Shrink`, apply the published arbitrary-sum identity, and pair the
resulting support membership with the public upper-bound law.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe w u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The `w`-small reindexing of the full supported family gives the same
actual subobject of `X`. -/
theorem simpleSupportSum_eq_subobjectSum_shrink
    [HasCoproducts.{w} C] (S : Set (ObjectClass C)) (X : C)
    [Small.{w} (simpleSupportSubobjects S X)] :
    letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
      hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
    simpleSupportSum S X =
      subobjectSum (fun i : Shrink.{w} (simpleSupportSubobjects S X) =>
        ((equivShrink (simpleSupportSubobjects S X)).symm i : Subobject X)) := by
  let : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
    hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
  let e := equivShrink.{w} (simpleSupportSubobjects S X)
  let F : Shrink.{w} (simpleSupportSubobjects S X) → Subobject X :=
    fun i => (e.symm i : Subobject X)
  change simpleSupportSum S X = subobjectSum F
  apply le_antisymm
  · apply simpleSupportSum_le S X
    intro P hP
    simpa only [F, Equiv.symm_apply_apply] using
      le_subobjectSum F (e ⟨P, hP⟩)
  · exact subobjectSum_le F fun i =>
      le_simpleSupportSum S X (e.symm i).property

/-- Renard A.IX: the actual supported-subobject sum is supported on `S`. -/
theorem simpleSupportSumSupport
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSumSupportStatement.{w} C := by
  intro hG
  let : HasCoproducts.{w} C := hG.1
  intro hAB6 S _hS X hsmall
  let : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
    hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
  let e := equivShrink.{w} (simpleSupportSubobjects S X)
  let F : Shrink.{w} (simpleSupportSubobjects S X) → Subobject X :=
    fun i => (e.symm i : Subobject X)
  have hsum : simpleSupportSum S X = subobjectSum F :=
    simpleSupportSum_eq_subobjectSum_shrink S X
  change simpleSubquotientClasses (simpleSupportSum S X : C) ⊆ S
  rw [hsum, simpleSubquotientSum C hG hAB6 X
    (Shrink.{w} (simpleSupportSubobjects S X)) F]
  intro q hq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
  exact (e.symm i).property hi

/-- The sum is the greatest actual supported subobject. -/
theorem simpleSupportSumMaximum
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSumMaximumStatement.{w} C := by
  intro hG
  let : HasCoproducts.{w} C := hG.1
  intro hAB6 S hS X hsmall
  let : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
    hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
  exact ⟨simpleSupportSumSupport C hG hAB6 S hS X,
    fun _ hP => le_simpleSupportSum S X hP⟩

/-- The exact public conjunction of source support and internal maximality. -/
theorem simpleSupportSumStatement
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportSumStatement.{w} C :=
  ⟨simpleSupportSumSupport C, simpleSupportSumMaximum C⟩

end

end Langlands.Renard
