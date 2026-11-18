import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityProof

/-! # Smooth-family representability on quasi-separated tests -/

universe u

namespace Langlands.AbelianScheme

/-- Every abelian scheme over a quasi-separated base admits an actual parameter scheme
carrying an actual universal rigidified smooth-family algebraically trivial family on
quasi-separated tests. The parameter is the underlying scheme of the shared
abelian-scheme representer, with the same family and the same universality proof. -/
theorem smoothFamilyQuasiSeparatedRepresentability :
    SmoothFamilyQuasiSeparatedRepresentabilityStatement.{u} := by
  intro S _ A
  obtain ⟨B, L, hL⟩ := smoothFamilyAbelianRepresentability.{u} S A
  exact ⟨B.X, L, hL⟩

end Langlands.AbelianScheme
