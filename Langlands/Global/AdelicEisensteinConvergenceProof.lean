import Langlands.Global.AdelicEisensteinMajorant
import Langlands.Global.AdelicPolynomialCosetRepresentatives

/-! # Absolute convergence of adelic Eisenstein series -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

/-- The adelic Eisenstein terms admit a compact-uniform summable majorant for sufficiently
regular parameters (Mœglin–Waldspurger II.1.5). -/
theorem eisensteinAbsoluteConvergence : EisensteinAbsoluteConvergenceStatement.{u} := by
  intro F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho
    _ _ φ _ _ hφ
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨n, j, σ, hσ⟩ := Chevalley.exists_line_stabilizer F G P p
    r.isCompatible.parabolic.isClosedSubgroup
  have hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range p) j := hσ
  have hrep := exists_polynomial_rationalCoset_representatives rho σ j hG
    r.isCompatible.parabolic hstab
  exact hK.exists_summable_eisenstein_majorant_of_projectiveRepresentatives r hA hT hG hU
    rho σ j hstab hrep φ hφ.1 hφ.2.2.2.2

end Langlands.Global
