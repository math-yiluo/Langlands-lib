import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityStatement

/-! # Reduction of the smooth-family representer to bases of finite type over `ℤ` -/

universe u

namespace Langlands.AbelianScheme

/-- If every abelian scheme over an affine base of finite type over `ℤ` admits the universal
smooth-family abelian-scheme parameter, then so does every abelian scheme over every
quasi-separated base. -/
def SmoothFamilyAbelianRepresentabilityOfFiniteTypeStatement : Prop :=
  FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} →
    SmoothFamilyAbelianRepresentabilityStatement.{u}

end Langlands.AbelianScheme
