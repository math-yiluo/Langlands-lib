import Langlands.Representation.Exponents.ShearRepresentation
import Langlands.Representation.Exponents.CommutativeUnipotentTempered

/-! # Renard VII.2.6, Remark: a tempered representation that is not unitarizable

The representation `x ↦ [[1, ord(x)], [0, 1]]` of `𝔾_m(k)` on `ℂ²` is tempered (its only
normalized exponent is trivial) and admits no invariant positive definite hermitian form.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme ShearRepresentation

/-- Renard VII.2.6, Remark: over every nonarchimedean local field, the shear representation
`x ↦ [[1, ord(x)], [0, 1]]` of `𝔾_m(k)` is tempered and not unitarizable. -/
theorem temperedReducibleNotUnitarizable :
    TemperedReducibleNotUnitarizableStatement.{u, v} := by
  intro k _ _ _ _ _
  refine ⟨Gm.group k, Gm.isConnectedReductive k, ?_⟩
  have := (Gm.isConnectedReductive k).isAffineHom
  let : TopologicalSpace (rationalPoints (Gm.group k)) := RationalPointFamily.pointTopology
  intro _ _
  refine ⟨SmoothRep.of (shearRep.{v} (Gm.gmValuation k)) (Gm.isSmooth_shearRep_gmValuation k),
    ?_, Gm.not_isUnitarizable_shearRep_gmValuation k⟩
  exact isNormalizedExponentTempered_of_mul_comm_of_sq_sub_one_eq_zero
    (Gm.isConnectedReductive k) _ (Gm.isAdmissible_shearRep_gmValuation k)
    (Gm.mul_comm_rationalPoints k) (sq_shearRep_sub_one _)

end Langlands.Aubert.General.RepresentedParabolic
