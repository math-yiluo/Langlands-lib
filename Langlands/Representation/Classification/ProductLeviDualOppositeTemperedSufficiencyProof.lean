import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof

/-!
# Product-Levi dual-opposite tempered sufficiency

The opposite dual-eigenfunctional form of product-Levi tempered sufficiency,
obtained by applying the published adapter from the upper generalized-exponent
core to the published proof of that core.
-/

namespace Langlands

universe uF uV

/-- Nonpositive within-block prefixes of every opposite Jacquet dual exponent
imply temperedness modulo the actual centre of the whole product Levi. -/
theorem glProductLeviDualOppositeTemperedSufficiency :
    GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV} :=
  glProductLeviDualOppositeTemperedSufficiency_of_core
    glProductLeviTemperedExponentSufficiency.{uF, uV}

end Langlands
