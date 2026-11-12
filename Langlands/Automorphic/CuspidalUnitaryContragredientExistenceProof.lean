import Langlands.Automorphic.CuspidalAdmissible.JointAdmissibility
import Langlands.Global.AdelicGLSiegelFinitenessProof

/-!
# Existence of actual unitary cuspidal contragredients

Every actual cuspidal realization with unitary central character has an actual cuspidal
contragredient with unitary central character. The proof combines joint admissibility of unitary
cuspidal realizations (given Siegel finiteness) with the proof of Siegel finiteness for the
adelic `GL_n` Siegel sets.
-/

universe uF

namespace Langlands.Automorphic

/-- **Contragredient existence.** -/
theorem cuspidalUnitaryContragredientExistence :
    CuspidalUnitaryContragredientExistenceStatement.{uF} :=
  CuspidalAdmissible.contragredientExistence_of_siegelFiniteness
    Langlands.Global.PrimitiveAdelicHeight.siegelSetGLFiniteness

end Langlands.Automorphic
