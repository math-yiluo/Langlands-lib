import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityStatement
import Langlands.GroupScheme.Torus.TorusUnirationalityStatement
import Langlands.GroupScheme.Unipotent.SplitAffineSpaceStatement

/-! # Statement: reduction of connected-group unirationality -/

universe u

namespace Langlands.GroupScheme

/-- The torus and split-unipotent affine-space statements imply connected-group
unirationality, including connected reductive groups over arbitrary fields. -/
def ConnectedGroupUnirationalityReductionStatement : Prop :=
  TorusUnirationalityStatement.{u} →
    SplitUnipotentAffineSpaceStatement.{u} →
      ConnectedGroupUnirationalityStatement.{u}

end Langlands.GroupScheme
