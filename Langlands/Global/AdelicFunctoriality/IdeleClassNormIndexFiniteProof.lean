import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexReduction
import Langlands.ClassField.Global.IntegralIdeleClassQuotientFinite

/-! # Proof of the idele-class norm index lemma -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- **Artin–Tate VI §1, first lemma.** For every extension of number fields `L/K`, in
independent universes, the range of the actual idele-class norm `C_L → C_K` has finite index,
and that index divides some power of `[L : K]`. -/
theorem ideleClassNormIndexFinite : IdeleClassNormIndexFinite.{u, v} :=
  ideleClassNormIndexFinite_of_integralIdeleClassQuotientFinite
    Langlands.ClassField.Global.integralIdeleClassQuotientFinite

end Langlands.Global.AdelicFunctoriality
