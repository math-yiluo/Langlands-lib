import Langlands.Representation.Derivative.MirabolicDerivativeVanishing

/-!
# Positive derivative detection for smooth mirabolic representations

The exact published detection statement follows from the independently published
rank induction in `MirabolicDerivativeVanishing`. See the paired Markdown for the
implemented argument, its BZ77 source, and the complete project dependency audit.
-/

namespace Langlands.Derivative

universe uF uV

/-- Every nonzero smooth mirabolic representation has positive derivative level. -/
theorem mirabolicDerivativeDetection {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicDerivativeDetection.{uF, uV} F T :=
  Mirabolic.derivativeDetection F T

end Langlands.Derivative
