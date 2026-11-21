import Langlands.GroupScheme.RelativeLevi.BorelSchemeReduction
import Langlands.GroupScheme.RelativeLevi.ParabolicSchemeProof

/-! # The scheme of Borel subgroups of a reductive group scheme -/

universe u

namespace Langlands.GroupScheme

/-- The functor of Borel subgroups of a reductive group scheme is represented
by a smooth proper scheme (Conrad, Theorem 5.2.11(3)). -/
theorem relativeBorelScheme : RelativeBorelSchemeStatement.{u} :=
  relativeBorelScheme_of_parabolicScheme relativeParabolicScheme.{u}

end Langlands.GroupScheme
