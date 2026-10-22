import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Index

/-! # The second inequality for the actual idele-class norm -/

noncomputable section

universe u v

namespace Langlands.Global.AdelicFunctoriality

/-- For a Galois extension of number fields, the index of the image of the
actual idele-class norm divides the extension degree. -/
def IdeleClassSecondInequality : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
      Module.finrank K L

end Langlands.Global.AdelicFunctoriality
