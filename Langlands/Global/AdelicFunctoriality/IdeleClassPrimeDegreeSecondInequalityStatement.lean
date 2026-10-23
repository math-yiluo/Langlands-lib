import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs

/-! # The prime-degree second inequality for actual idele classes -/

noncomputable section

universe u v

namespace Langlands.Global.AdelicFunctoriality

/-- For a Galois extension of number fields of prime degree, the index of the
image of the actual idele-class norm divides the extension degree. -/
def IdeleClassPrimeDegreeSecondInequality : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    Nat.Prime (Module.finrank K L) →
      (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
        Module.finrank K L

end Langlands.Global.AdelicFunctoriality
