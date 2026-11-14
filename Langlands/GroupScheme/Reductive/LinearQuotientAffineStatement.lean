import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

/-! # Affineness of actual linear quotients by connected reductive subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every supplied homogeneous quotient of a general linear group by an actual closed
connected reductive subgroup over an algebraically closed field is affine. -/
def ReductiveLinearQuotientAffineStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ →
      ∀ (Q : HomogeneousQuotientFromEmbedding.HomogeneousQuotient ρ),
        IsAffineHom Q.scheme.hom

end Langlands.GroupScheme
