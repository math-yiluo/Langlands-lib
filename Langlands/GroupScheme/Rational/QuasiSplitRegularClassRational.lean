import Langlands.GroupScheme.Rational.QuasiSplitRegularClassRationalReduction
import Langlands.GroupScheme.Rational.QuasiSplitSteinbergQuotient

/-! # Rational points of Galois-stable strongly regular classes (Borel–Springer 8.6) -/

universe u

namespace Langlands.GroupScheme

/-- **Borel–Springer 8.6 for Galois-stable strongly regular classes.** Let `G` be a simply
connected quasi-split group over a field `K` and `L/K` a finite Galois extension. A strongly
regular `L`-point of `G` whose geometric conjugacy class is stable under `Gal(L/K)` is
geometrically conjugate to a `K`-rational point. -/
theorem quasiSplitRegularClassRational : QuasiSplitRegularClassRationalStatement.{u} :=
  quasiSplitRegularClassRationalReduction quasiSplitSteinbergQuotient

end Langlands.GroupScheme
