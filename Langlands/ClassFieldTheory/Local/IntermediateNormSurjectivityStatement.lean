import Langlands.ClassFieldTheory.Local.Norms
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # Inheritance of all intermediate-field norm surjectivity -/

namespace Langlands.ClassFieldTheory.Local

/-- Surjectivity of the determinant norm to every intermediate field is inherited
by the base norm, all lower extensions, and all upper extensions. -/
def IntermediateNormSurjectivityInheritance.{u} : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L],
    (∀ E : IntermediateField K L,
      letI : FiniteDimensional E L := FiniteDimensional.right K E L
      Function.Surjective (Langlands.LocalClassField.normUnits E L)) →
    Function.Surjective (Langlands.LocalClassField.normUnits K L) ∧
    (∀ E : IntermediateField K L,
      letI : FiniteDimensional K E := FiniteDimensional.left K E L
      Function.Surjective (Langlands.LocalClassField.normUnits K E)) ∧
    (∀ (E : IntermediateField K L) (F : IntermediateField K E),
      letI : FiniteDimensional K E := FiniteDimensional.left K E L
      letI : FiniteDimensional F E := FiniteDimensional.right K F E
      Function.Surjective (Langlands.LocalClassField.normUnits F E)) ∧
    (∀ (E : IntermediateField K L) (F : IntermediateField E L),
      letI : FiniteDimensional F L :=
        FiniteDimensional.right K (F.restrictScalars K) L
      Function.Surjective (Langlands.LocalClassField.normUnits F L))

end Langlands.ClassFieldTheory.Local
