import Langlands.Representation.Whittaker.InducedWhittakerTypeReductionProof
import Langlands.Representation.Whittaker.InducedLocalizationProof

/-! # Whittaker type of upper block induction

The closed character-localization theorem supplies the geometric input to the
published algebraic reduction, proving the original functional-space iff.
-/

namespace Langlands

universe uF uV

/-- Upper unnormalized block induction has a one-dimensional space of Whittaker
functionals exactly when every inducing block does. -/
theorem inducedWhittakerType : InducedWhittakerTypeStatement.{uF, uV} :=
  inducedWhittakerTypeReduction.{uF, uV} inducedLocalization.{uF, uV}

end Langlands
