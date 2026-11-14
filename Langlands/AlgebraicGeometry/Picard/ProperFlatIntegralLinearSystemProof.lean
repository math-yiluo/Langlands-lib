import Langlands.AlgebraicGeometry.Picard.LinearSystemFlatness

/-! # The linear system of an invertible module on a proper flat family with integral fibres

Proof of `ProperFlatIntegralLinearSystemStatement` (Kleiman, *The Picard scheme*, Theorem 3.13
and Exercise 3.11, with EGA III 7.7.6): the linear system is glued from Grassmannians of rank-one
quotients over the affine opens of the base, and the flatness clause is checked on those affine
opens. -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- **Kleiman's linear system** of an invertible module on a proper flat family with geometrically
integral fibres over a locally noetherian base. -/
theorem properFlatIntegralLinearSystem : ProperFlatIntegralLinearSystemStatement.{u} :=
  LinearSystemGluing.properFlatIntegralLinearSystem_of_localFibreFlatness
    LinearSystemCechModule.localFibreFlatness

end Langlands.AlgebraicGeometry.Picard
