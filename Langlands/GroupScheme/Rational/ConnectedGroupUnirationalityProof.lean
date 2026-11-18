import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Torus.TorusUnirationalityProof
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceProof

/-! # Proof: unirationality of connected group varieties -/

universe u

namespace Langlands.GroupScheme

/-- **Unirationality of connected group varieties** (Milne, *Algebraic Groups* (2017),
Theorem 17.93). Smooth connected affine groups over perfect fields and connected
reductive groups over arbitrary fields are unirational. -/
theorem connectedGroupUnirationality : ConnectedGroupUnirationalityStatement.{u} :=
  connectedGroupUnirationalityReduction torusUnirationality
    splitUnipotentAffineSpaceStatement

end Langlands.GroupScheme
