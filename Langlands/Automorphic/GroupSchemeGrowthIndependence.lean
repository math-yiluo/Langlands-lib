import Langlands.Global.RepresentationGrowthIndependence
import Langlands.Automorphic.GroupSchemeGrowth

/-! # Closed-embedding independence of actual adelic slice-growth spaces -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {N M : ℕ}
  (rho : GroupScheme.MatrixRepresentation G (Fin N))
  (sigma : GroupScheme.MatrixRepresentation G (Fin M))

/-- Independence is applied separately on each original finite adelic slice. -/
theorem hasPolynomialGrowth_iff_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : ContinuousRationalFunctions F G) :
    HasPolynomialGrowth F G rho f ↔ HasPolynomialGrowth F G sigma f := by
  apply forall_congr'
  intro b
  exact RepresentationGrowth.hasPolynomialGrowth_iff_of_closedImmersions
    F G rho sigma hrho hsigma (infiniteSlice F G b f)

/-- The actual slice-growth subrepresentations are equal in their common
continuous rational-function representation. -/
theorem polynomialGrowthSubrepresentation_eq_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    polynomialGrowthSubrepresentation F G rho =
      polynomialGrowthSubrepresentation F G sigma := by
  ext f
  change (f ∈ polynomialGrowthSubrepresentation F G rho) ↔
    (f ∈ polynomialGrowthSubrepresentation F G sigma)
  rw [mem_polynomialGrowthSubrepresentation, mem_polynomialGrowthSubrepresentation]
  exact hasPolynomialGrowth_iff_of_closedImmersions F G rho sigma hrho hsigma f

/-- Changing the closed embedding preserves the original continuous function. -/
def polynomialGrowthChangeRepresentation
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    PolynomialGrowthRationalFunctions F G rho ≃ₗ[ℂ]
      PolynomialGrowthRationalFunctions F G sigma :=
  LinearEquiv.ofEq _ _ (congrArg Subrepresentation.toSubmodule
    (polynomialGrowthSubrepresentation_eq_of_closedImmersions F G rho sigma hrho hsigma))

@[simp] theorem polynomialGrowthChangeRepresentation_val
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : PolynomialGrowthRationalFunctions F G rho) :
    (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f).val = f.val := by
  exact LinearEquiv.coe_ofEq_apply _ f

/-- The full original adelic actions are intertwined with their positive sign. -/
theorem polynomialGrowthChangeRepresentation_rightAction
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : PolynomialGrowthRationalFunctions F G rho) (g : AdelicGroupPoints F G) :
    polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma
        (polynomialGrowthRightAction F G rho g f) =
      polynomialGrowthRightAction F G sigma g
        (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f) := by
  apply Subtype.ext
  rw [polynomialGrowthChangeRepresentation_val]
  change continuousRightAction F G g f.val = continuousRightAction F G g
    (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f).val
  rw [polynomialGrowthChangeRepresentation_val]

/-- The common ambient inclusion is independent of the closed embedding too. -/
theorem polynomialGrowthChangeRepresentation_inclusion
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : PolynomialGrowthRationalFunctions F G rho) :
    polynomialGrowthInclusion F G sigma
        (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f) =
      polynomialGrowthInclusion F G rho f := by
  change (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f).val = f.val
  exact polynomialGrowthChangeRepresentation_val F G rho sigma hrho hsigma f

/-- Adding infinite plot smoothness and slice-local finite regularity retains
the same independence. -/
theorem plotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    plotSmoothPolynomialGrowthSubrepresentation F G rho =
      plotSmoothPolynomialGrowthSubrepresentation F G sigma := by
  unfold plotSmoothPolynomialGrowthSubrepresentation
  rw [polynomialGrowthSubrepresentation_eq_of_closedImmersions F G rho sigma hrho hsigma]

/-- The stronger common-open-finite-stabilizer intersection is independent too. -/
theorem finitePlotSmoothPolynomialGrowthSubrepresentation_eq_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    finitePlotSmoothPolynomialGrowthSubrepresentation F G rho =
      finitePlotSmoothPolynomialGrowthSubrepresentation F G sigma := by
  unfold finitePlotSmoothPolynomialGrowthSubrepresentation
  rw [polynomialGrowthSubrepresentation_eq_of_closedImmersions F G rho sigma hrho hsigma]

end Langlands.Automorphic.GroupSchemeFunctions
