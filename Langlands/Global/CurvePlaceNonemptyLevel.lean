import Langlands.Global.CurvePlaceAdeleRing
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCommRingCat

/-! # Actual curve-place adelic diagrams indexed by nonempty finite sets -/

noncomputable section

universe u

open CategoryTheory Limits
open scoped Classical

namespace Langlands.Global

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The source's finite nonempty indexing convention, using actual curve places. -/
abbrev CurvePlaceNonemptyLevelIndex :=
  {S : Finset (AlgebraicCurve.Place k F) // S.Nonempty}

/-- Forget the nonemptiness proof, preserving the inclusion order. -/
def curvePlaceNonemptyLevelForget :
    CurvePlaceNonemptyLevelIndex k F →o Finset (AlgebraicCurve.Place k F) where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

/-- Insert a supplied actual place to obtain a nonempty level above any finite level. -/
def curvePlaceNonemptyLevelEnlarge (p : AlgebraicCurve.Place k F) :
    Finset (AlgebraicCurve.Place k F) →o CurvePlaceNonemptyLevelIndex k F := by
  classical
  exact
    { toFun := fun S => ⟨insert p S, Finset.insert_nonempty p S⟩
      monotone' := fun _ _ h => Finset.insert_subset_insert p h }

@[simp]
theorem curvePlaceNonemptyLevelEnlarge_val (p : AlgebraicCurve.Place k F)
    (S : Finset (AlgebraicCurve.Place k F)) :
    (curvePlaceNonemptyLevelEnlarge k F p S).val = insert p S := rfl

theorem curvePlaceNonemptyLevelEnlarge_le (p : AlgebraicCurve.Place k F)
    (S : Finset (AlgebraicCurve.Place k F)) :
    S ⊆ (curvePlaceNonemptyLevelEnlarge k F p S).val := by
  classical
  exact Finset.subset_insert p S

theorem curvePlaceNonemptyLevelIndex_cofinal (p : AlgebraicCurve.Place k F)
    (S : Finset (AlgebraicCurve.Place k F)) :
    ∃ T : CurvePlaceNonemptyLevelIndex k F, S ⊆ T.val :=
  ⟨curvePlaceNonemptyLevelEnlarge k F p S, curvePlaceNonemptyLevelEnlarge_le k F p S⟩

/-- Union supplies a concrete common upper bound within the nonempty index type. -/
def curvePlaceNonemptyLevelUnion (S T : CurvePlaceNonemptyLevelIndex k F) :
    CurvePlaceNonemptyLevelIndex k F := by
  classical
  exact ⟨S.val ∪ T.val, S.property.mono Finset.subset_union_left⟩

theorem curvePlaceNonemptyLevelUnion_left (S T : CurvePlaceNonemptyLevelIndex k F) :
    S ≤ curvePlaceNonemptyLevelUnion k F S T := by
  classical
  exact Finset.subset_union_left

theorem curvePlaceNonemptyLevelUnion_right (S T : CurvePlaceNonemptyLevelIndex k F) :
    T ≤ curvePlaceNonemptyLevelUnion k F S T := by
  classical
  exact Finset.subset_union_right

theorem curvePlaceNonemptyLevelIndex_directed :
    Directed (· ≤ ·) (id : CurvePlaceNonemptyLevelIndex k F →
      CurvePlaceNonemptyLevelIndex k F) :=
  fun S T => ⟨curvePlaceNonemptyLevelUnion k F S T,
    curvePlaceNonemptyLevelUnion_left k F S T, curvePlaceNonemptyLevelUnion_right k F S T⟩

/-- The actual open adelic level subrings, indexed by all finite nonempty sets of places. -/
def curvePlaceNonemptyAdeleLevelDiagram :
    CurvePlaceNonemptyLevelIndex k F ⥤ TopCommRingCat.{u} where
  obj S := TopCommRingCat.of (curvePlaceAdeleLevel k F S.val)
  map {S T} h := ⟨curvePlaceAdeleLevelMap k F (leOfHom h), by
    apply Continuous.subtype_mk
    exact continuous_subtype_val⟩
  map_id _ := by
    apply Subtype.ext
    ext a
    rfl
  map_comp _ _ := by
    apply Subtype.ext
    ext a
    rfl

/-- The ambient restricted product and its literal continuous level inclusions. -/
def curvePlaceNonemptyAdeleLevelCocone :
    Cocone (curvePlaceNonemptyAdeleLevelDiagram k F) where
  pt := TopCommRingCat.of (CurvePlaceAdeleRing k F)
  ι :=
    { app := fun S => ⟨(curvePlaceAdeleLevel k F S.val).subtype, continuous_subtype_val⟩
      naturality := by
        intro S T h
        apply Subtype.ext
        ext a
        rfl }

/-- The same diagram in commutative rings. -/
def curvePlaceNonemptyAdeleLevelRingDiagram :
    CurvePlaceNonemptyLevelIndex k F ⥤ CommRingCat.{u} :=
  curvePlaceNonemptyAdeleLevelDiagram k F ⋙ forget₂ TopCommRingCat CommRingCat

/-- The same canonical cocone after forgetting topology. -/
def curvePlaceNonemptyAdeleLevelRingCocone :
    Cocone (curvePlaceNonemptyAdeleLevelRingDiagram k F) :=
  (forget₂ TopCommRingCat CommRingCat).mapCocone (curvePlaceNonemptyAdeleLevelCocone k F)

end Langlands.Global
