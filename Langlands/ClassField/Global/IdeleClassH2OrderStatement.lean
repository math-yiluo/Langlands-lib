import Langlands.ClassField.Global.Cohomology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! # The order bound for second idele-class cohomology -/

namespace Langlands.ClassField.Global

universe u v

/-- For every Galois extension of number fields, the actual second idele-class
cohomology group is finite and its order divides the extension degree.
This states the number-field case of Artin–Tate XIV §3, printed p.152. -/
def IdeleClassH2OrderBound : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (E : Type v) [Field E] [NumberField E] [Algebra F E] [IsGalois F E],
    Finite (relativeIdeleClassCohomology F E 2 : Type v) ∧
      Nat.card (relativeIdeleClassCohomology F E 2 : Type v) ∣ Module.finrank F E

end Langlands.ClassField.Global
