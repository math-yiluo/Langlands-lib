import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.SemilocalEquationTCStatements
import Langlands.Global.RankinSelberg.UnequalFactorizationAtStatement

/-! # The unequal-rank semi-local equation from factorization over totally complex fields

A variant of the semi-local reduction in which factorization is required only over totally
complex fields. See the paired Markdown.
-/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The unequal-rank semi-local functional equation over totally complex number fields
follows from the complex-place unequal-rank functional equation and the integrated
factorization over totally complex fields. The central sign is available separately. -/
def UnequalSemilocalFieldwiseTCReductionStatement : Prop :=
  ComplexUnequalFunctionalEquationStatement.{u} →
    UnequalArchimedeanFactorizationTCStatement.{u, uQ} →
      UnequalSemilocalEquationTCStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
