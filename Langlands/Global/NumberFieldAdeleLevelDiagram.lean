import Langlands.Global.NumberFieldAdeleLevel
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Topology.Category.TopCommRingCat

/-! # The actual full number-field adelic level diagram and its canonical cocone -/

noncomputable section

universe u

open CategoryTheory Limits

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- Actual full number-field adelic levels, ordered by inclusion, as topological commutative rings. -/
def numberFieldAdeleLevelDiagram : Finset (FinitePlace K) ⥤ TopCommRingCat.{u} where
  obj S := TopCommRingCat.of (numberFieldAdeleLevel K S)
  map {S T} h := ⟨numberFieldAdeleLevelMap K (leOfHom h), by
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

/-- The ambient full number-field adele ring, with its actual continuous level inclusions. -/
def numberFieldAdeleLevelCocone : Cocone (numberFieldAdeleLevelDiagram K) where
  pt := TopCommRingCat.of (Adeles K)
  ι :=
    { app := fun S => ⟨(numberFieldAdeleLevel K S).subtype, continuous_subtype_val⟩
      naturality := by
        intro S T h
        apply Subtype.ext
        ext a
        rfl }

/-- The same actual level diagram after forgetting topology. -/
def numberFieldAdeleLevelRingDiagram : Finset (FinitePlace K) ⥤ CommRingCat.{u} :=
  numberFieldAdeleLevelDiagram K ⋙ forget₂ TopCommRingCat CommRingCat

/-- The same canonical cocone in the category of commutative rings. -/
def numberFieldAdeleLevelRingCocone : Cocone (numberFieldAdeleLevelRingDiagram K) :=
  (forget₂ TopCommRingCat CommRingCat).mapCocone (numberFieldAdeleLevelCocone K)

end Langlands.Global
