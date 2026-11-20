import Langlands.GroupScheme.Rational.SemistandardSpectralFinitenessProof

/-! # Finiteness and nonemptiness of the actual semistandard Levi fibers -/

universe u

namespace Langlands.GroupScheme

/-- Each actual indexed Levi has a finite, nonempty parabolic fiber. -/
theorem semistandardSpectralFiberFiniteness :
    SemistandardSpectralFiberFinitenessStatement.{u} :=
  semistandardSpectralFiberFiniteness_of_finiteness semistandardSpectralFiniteness

end Langlands.GroupScheme
