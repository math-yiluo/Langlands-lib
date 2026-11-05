import Langlands.GroupScheme.Rational.CommutingFactorizationIntegrality
import Langlands.GroupScheme.Rational.PositivePowerFactorizationProof

/-! # Spectral integrality for anisotropic reductive groups over local fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Anisotropy forces every characteristic coefficient of every actual
finite-dimensional rational-point representation matrix into the valuation ring. -/
theorem anisotropicSpectralIntegrality :
    AnisotropicSpectralIntegralityStatement.{u} := by
  intro F _ _ _ _ G hG ha N ρ g j
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let D := positivePowerFactorizationData G g
  exact ρ.charpoly_coeff_vle_one_of_pow_eq_torus_mul_additive ha g
    D.exponent_pos D.inclusion D.point D.additive D.isTorus D.closed
    D.factorization D.commute j

end Langlands.GroupScheme
