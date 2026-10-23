import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Mathlib.GroupTheory.Index

/-! # Finiteness and the degree-power bound for the idele-class norm index -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- For every extension of number fields, the image of the actual idele-class
norm has finite index, and that index divides some power of the relative degree.
This states the first lemma of Artin–Tate VI §1, printed p.20. -/
def IdeleClassNormIndexFinite : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L],
    let H := (ideleClassNorm (K := K) (L := L)).toMonoidHom.range
    H.FiniteIndex ∧ ∃ r : ℕ, H.index ∣ (Module.finrank K L) ^ r

end Langlands.Global.AdelicFunctoriality
