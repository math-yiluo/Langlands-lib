import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Renard A.II.2: categories in the fixed-dimension vector-space example

The one-object category is the actual full singleton subcategory on the
coordinate space; its morphisms are every linear endomorphism. The
quasi-inverse comparison is a separate statement and proof.
-/

open CategoryTheory

namespace Langlands.Renard

/-- Actual finite-dimensional vector spaces of one prescribed dimension. -/
def fixedDimensionVectorSpaceObjects.{u, v} (k : Type u) [Field k] (n : ℕ) :
    ObjectProperty (ModuleCat.{max u v} k) :=
  fun X => FiniteDimensional k X ∧ Module.finrank k X = n

/-- Vector spaces of dimension `n`, with all linear maps. -/
abbrev FixedDimensionVectorSpaces.{u, v} (k : Type u) [Field k] (n : ℕ) :=
  (fixedDimensionVectorSpaceObjects.{u, v} k n).FullSubcategory

instance fixedDimension_finite.{u, v} (k : Type u) [Field k] (n : ℕ)
    (X : FixedDimensionVectorSpaces.{u, v} k n) : FiniteDimensional k X.obj :=
  X.property.1

/-- Every object has the specified dimension, including when `n = 0`. -/
theorem fixedDimension_finrank.{u, v} (k : Type u) [Field k] (n : ℕ)
    (X : FixedDimensionVectorSpaces.{u, v} k n) : Module.finrank k X.obj = n :=
  X.property.2

/-- The coordinate space, lifted into the common carrier universe. -/
abbrev standardCoordinateVectorSpace.{u, v} (k : Type u) [Field k] (n : ℕ) :
    ModuleCat.{max u v} k :=
  ModuleCat.of k (ULift.{v} (Fin n → k))

/-- The coordinate space as an object of the dimension-`n` category. -/
def standardCoordinateObject.{u, v} (k : Type u) [Field k] (n : ℕ) :
    FixedDimensionVectorSpaces.{u, v} k n :=
  ⟨standardCoordinateVectorSpace.{u, v} k n, by
    constructor
    · infer_instance
    · change Module.finrank k (ULift.{v} (Fin n → k)) = n
      rw [finrank_ulift, Module.finrank_pi, Fintype.card_fin]⟩

/-- The singleton object property on the actual coordinate object. -/
def standardCoordinateObjects.{u, v} (k : Type u) [Field k] (n : ℕ) :
    ObjectProperty (FixedDimensionVectorSpaces.{u, v} k n) :=
  fun X => X = standardCoordinateObject.{u, v} k n

/-- The source's one-object category, retaining all endomorphisms. -/
abbrev OneObjectVectorSpaceCategory.{u, v} (k : Type u) [Field k] (n : ℕ) :=
  (standardCoordinateObjects.{u, v} k n).FullSubcategory

/-- Its distinguished object is the coordinate space itself. -/
def oneObjectVectorSpace.{u, v} (k : Type u) [Field k] (n : ℕ) :
    OneObjectVectorSpaceCategory.{u, v} k n :=
  ⟨standardCoordinateObject.{u, v} k n, rfl⟩

/-- The category has exactly the displayed single object. -/
theorem oneObjectVectorSpace_unique.{u, v} (k : Type u) [Field k] (n : ℕ)
    (X : OneObjectVectorSpaceCategory.{u, v} k n) :
    X = oneObjectVectorSpace.{u, v} k n := by
  apply ObjectProperty.FullSubcategory.ext
  exact X.property

/-- The actual inclusion of the one-object full subcategory. -/
abbrev fixedDimensionVectorSpaceInclusion.{u, v} (k : Type u) [Field k] (n : ℕ) :
    OneObjectVectorSpaceCategory.{u, v} k n ⥤ FixedDimensionVectorSpaces.{u, v} k n :=
  (standardCoordinateObjects.{u, v} k n).ι

/-- An actual chosen linear isomorphism from the coordinate object. -/
noncomputable def coordinateVectorSpaceIso.{u, v} (k : Type u) [Field k] (n : ℕ)
    (X : FixedDimensionVectorSpaces.{u, v} k n) :
    standardCoordinateObject.{u, v} k n ≅ X :=
  (fixedDimensionVectorSpaceObjects.{u, v} k n).isoMk
    ((LinearEquiv.ofFinrankEq (R := k)
      (standardCoordinateVectorSpace.{u, v} k n) X.obj
      (by
        change Module.finrank k (ULift.{v} (Fin n → k)) = Module.finrank k X.obj
        rw [finrank_ulift, Module.finrank_pi, Fintype.card_fin]
        exact (fixedDimension_finrank k n X).symm)).toModuleIso)

end Langlands.Renard
