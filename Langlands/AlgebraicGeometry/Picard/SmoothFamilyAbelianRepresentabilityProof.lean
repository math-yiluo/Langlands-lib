import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof

/-! # The shared abelian-scheme representer for smooth-family Picard classes -/

universe u

namespace Langlands.AbelianScheme

/-- Every abelian scheme over a quasi-separated base admits an abelian-scheme parameter
carrying an actual universal rigidified smooth-family algebraically trivial family on all
quasi-separated tests. -/
theorem smoothFamilyAbelianRepresentability :
    SmoothFamilyAbelianRepresentabilityStatement.{u} :=
  smoothFamilyAbelianRepresentabilityOfFiniteType.{u}
    finiteTypeSmoothFamilyAbelianRepresentability.{u}

end Langlands.AbelianScheme
