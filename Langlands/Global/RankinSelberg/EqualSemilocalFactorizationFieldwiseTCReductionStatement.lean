import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.EqualFactorizationAtStatement
import Langlands.Global.RankinSelberg.EqualSemilocalReductionTC

/-! # The equal-rank semi-local factorization premise from totally complex data

A variant of the totally complex reduction of the equal-rank factorization premise.
It assumes integrated factorization only over totally complex fields.
-/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The equal-rank semi-local factorization premise over totally complex fields follows
from the complex-place equal-rank functional equation and integrated equal-rank
factorization over totally complex fields. The central sign is available separately. -/
def EqualSemilocalFactorizationFieldwiseTCReductionStatement : Prop :=
  ComplexEqualFunctionalEquationStatement.{u} →
    EqualArchimedeanFactorizationTCStatement.{u, uQ} →
      EqualSemilocalFactorizationTCStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
