import Langlands.GroupScheme.RelativeIdentityComponent
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Homogeneous quotient for a closed relative identity component -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- The representability step in Conrad's proof of Proposition 3.1.3:
when the relative identity component is closed, its right-coset quotient
is a separated finitely presented scheme with the actual quotient map. -/
def ClopenQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom]
    [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    (H : GroupScheme S) (i : H ⟶ G),
    IsRelativeIdentityComponent G i → IsClosedImmersion i.hom.hom.left →
    Nonempty (HomogeneousQuotientFromEmbedding.HomogeneousQuotient i)

end Langlands.GroupScheme.RelativeIdentityComponent
