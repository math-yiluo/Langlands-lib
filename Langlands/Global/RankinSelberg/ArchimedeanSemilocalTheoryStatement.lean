import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationStatement
import Langlands.Global.RankinSelberg.ArchimedeanCentralSignStatement

/-! # The archimedean Rankin–Selberg theory behind the semi-local functional equations

The three statements needed by the premises `UnequalSemilocalFactorizationStatement` and
`EqualSemilocalFactorizationStatement`, in both rank cases: the archimedean local functional
equation (Jacquet 2009, Theorem 2.1; Cogdell 2004, Theorems 3.5–3.6), the factorization of the
partial integrals over `S` and the infinite places, and the central sign (Cogdell 2004,
pp.219–220). The paired Markdown sketches how they imply both premises, and how, over a
totally complex field, the complex-place part suffices.
-/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **The archimedean semi-local theory, both ranks**: result 1 at the complex and at the real
places, the factorization over `S` and the infinite places (result 2), and the central sign
(result 3). -/
def ArchimedeanSemilocalTheoryStatement : Prop :=
  ArchimedeanFunctionalEquationStatement.{u} ∧ ArchimedeanFactorizationStatement.{u, uQ} ∧
    ArchimedeanCentralSignStatement.{u, uQ}

/-- **The complex-place semi-local theory, both ranks**: result 1 at the complex places only,
with results 2 and 3. Over a totally complex field it implies both premises. -/
def ComplexSemilocalTheoryStatement : Prop :=
  ComplexPlaceFunctionalEquationStatement.{u} ∧ ArchimedeanFactorizationStatement.{u, uQ} ∧
    ArchimedeanCentralSignStatement.{u, uQ}

end Langlands.Global.RankinSelbergGlobal
