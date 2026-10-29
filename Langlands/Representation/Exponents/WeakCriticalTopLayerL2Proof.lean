import Langlands.Representation.Exponents.WeakCriticalTopLayerL2Reduction
import Langlands.Representation.Classification.ProductLeviDualOppositeSquareIntegrableSufficiencyProof

/-!
# Square-integrability of quotients of the maximal layer of a weakly critical exponent

Every irreducible quotient of the maximal layer of a weakly critical dual
exponent of an irreducible tempered representation of `GL_n` is
square-integrable modulo the centre of the Levi, for every Borel Haar measure.
This combines the reduction to the product-Levi square-integrability criterion
with the proof of that criterion.
-/

namespace Langlands

universe uF uV uW

/-- Irreducible quotients of the maximal layer of a weakly critical dual
exponent of an irreducible tempered representation are square-integrable modulo
the centre of the Levi, for every Borel Haar measure. -/
theorem glWeaklyCriticalTopLayerL2 : GLWeaklyCriticalTopLayerL2Statement.{uF, uV, uW} :=
  glWeaklyCriticalTopLayerL2_of glProductLeviDualOppositeSquareIntegrableSufficiency.{uF, uW}

end Langlands
