import Langlands.Representation.Archimedean.ComplexDuality.Pairing
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance

/-!
# Duality of complex principal series with inverse characters

Proof of `Langlands.Archimedean.ComplexStandardDualityStatement`: the integration pairing
`⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk` is invariant and nondegenerate in the second argument.
-/

noncomputable section

namespace Langlands.Archimedean

open ComplexDuality

set_option backward.isDefEq.respectTransparency false

/-- The `U(n)`-finite functions of the principal series of pointwise inverse complex position
characters are in invariant duality, nondegenerate in the second argument, through the
integration pairing over `U(n)`. -/
theorem complexStandardDuality : ComplexStandardDualityStatement :=
  complexStandardDuality_of_lieInvariance fun n χ χ' hχ _ _ hf hh X =>
    integral_rightDerivative_mul_add_eq_zero (unitaryHaar n) χ χ' hχ hf hh X

end Langlands.Archimedean
