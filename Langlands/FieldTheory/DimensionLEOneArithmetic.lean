import Langlands.FieldTheory.DimensionLEOne
import Langlands.ClassFieldTheory.Local.FiniteNormH2Proof
import Mathlib.FieldTheory.SeparableDegree

/-! # Arithmetic consequences of the dimension-one norm criterion -/

universe u

namespace Langlands.FieldTheory

/-- Every finite Galois extension has trivial actual relative second cohomology. -/
def HasTrivialFiniteRelativeH2 (K : Type u) [Field K] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    Subsingleton (Langlands.ClassFieldTheory.Local.relativeCohomology K L 2)

/-- The dimension-one norm criterion is preserved by finite separable extension. -/
theorem HasDimensionLEOne.finite_separable_extension
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hK : HasDimensionLEOne K) : HasDimensionLEOne E := by
  intro F _ _ _ _ L _ _ _ _
  let : Algebra K F := ((algebraMap E F).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : FiniteDimensional K F := FiniteDimensional.trans K E F
  let : Algebra.IsSeparable K F := Algebra.IsSeparable.trans K E F
  exact hK F L

/-- The norm criterion supplies every intermediate-field norm needed by the
published finite-Galois relative second-cohomology vanishing theorem. -/
theorem HasDimensionLEOne.trivial_finite_relative_h2
    {K : Type u} [Field K] (hK : HasDimensionLEOne K) :
    HasTrivialFiniteRelativeH2 K := by
  intro L _ _ _ _
  apply Langlands.ClassFieldTheory.Local.finiteNormH2Vanishing K L
  intro E
  let : FiniteDimensional K E := IntermediateField.finiteDimensional_left E
  let : Algebra.IsSeparable K E :=
    Algebra.isSeparable_tower_bot_of_isSeparable K E L
  let : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  exact hK E L

end Langlands.FieldTheory
