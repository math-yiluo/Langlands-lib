import Langlands.BaseChange.TwistedInducedCharacterFormulaFromLocalDescent
import Langlands.BaseChange.TwistedLocalDescent.Proof

/-! # The twisted induced character formula

Henniart–Lemaire (2011), II.4.5 (3): the twisted character of a σ-stable parabolically induced
representation of `GL_n(E)` at a σ-regular point is the sum, over the Levi classes of the norm, of
the twisted characters of the inducing data weighted by the relative discriminant. It follows
from the reduction `twistedInducedCharacterFormula_of_localDescent` (which uses the twisted van
Dijk formula) and the local descent of the twisted constant term
(`TwistedLocalDescent.twistedLocalDescent`). See the paired Markdown.
-/

namespace Langlands.BaseChange

universe u v uW

/-- **The twisted induced character formula** (Henniart–Lemaire 2011, II.4.5 (3)). -/
theorem twistedInducedCharacterFormula : TwistedInducedCharacterFormulaStatement.{u, v, uW} :=
  twistedInducedCharacterFormula_of_localDescent TwistedLocalDescent.twistedLocalDescent

end Langlands.BaseChange
