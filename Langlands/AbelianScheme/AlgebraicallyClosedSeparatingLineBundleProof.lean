import Langlands.AbelianScheme.AlgebraicallyClosedSeparatingLineBundleStatement
import Langlands.AbelianScheme.SeparatingLineBundle.Assembly
import Langlands.AbelianScheme.FieldTheoremOfTheSquareProof

/-! # A separating line bundle over an algebraically closed field

The finite section seed and the theorem of the square yield a line bundle whose
complete linear system is base-point free and separates rational points and
nonzero dual-number tangent vectors.
-/

universe u

namespace Langlands.GroupScheme

/-- Every commutative smooth proper geometrically connected group scheme over
an algebraically closed field carries a line bundle separating rational points
and nonzero tangent vectors, with a base-point-free complete linear system. -/
theorem algebraicallyClosedSeparatingLineBundle :
    AlgebraicallyClosedSeparatingLineBundleStatement.{u} :=
  SeparatingLineBundle.algebraicallyClosedSeparatingLineBundle_of_square
    fieldTheoremOfTheSquare.{u}

end Langlands.GroupScheme
