import Langlands.GroupScheme.Rational.CompactPointsAnisotropy
import Langlands.GroupScheme.Rational.ReductiveSpectralBoundednessProof
import Langlands.GroupScheme.Rational.AnisotropicSpectralIntegralityProof

/-! # Compact rational points are equivalent to anisotropy over local fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

/-- The full canonical rational-point space of a connected reductive group over
a nonarchimedean local field is compact exactly when the group has split rank zero. -/
theorem anisotropicCompactness_proof : AnisotropicCompactnessStatement.{u} := by
  intro F _ _ _ _ G hG
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  constructor
  · exact compactPointsAnisotropy_proof F G
  · exact anisotropicPointsCompactness_of_spectral
      reductiveSpectralBoundedness anisotropicSpectralIntegrality F G hG

end Langlands.GroupScheme
