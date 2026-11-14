import Langlands.Geometry.Building.KPUnramifiedComparisonLeviContainment
import Langlands.Geometry.Building.KPUnramifiedComparisonLeviGeometry

/-! # The Levi field of concrete unramified apartment lifts -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open TensorProduct
open Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

set_option maxHeartbeats 1000000 in
/-- Every concrete unramified apartment lift satisfies the Levi field. -/
theorem unramifiedComparisonLeviField : UnramifiedComparisonLeviFieldStatement.{u} := by
  intro F _ _ _ _ G _ P _ t L
  obtain ⟨ξ, _, hconst⟩ := L.exists_generic_levi_geometry
  refine ⟨descentCocharacterMap F (UnramifiedClosure F) t.f
    P.isMaximalSplitTorus.isSplitSubtorus.1 ((1 : ℝ) ⊗ₜ[ℤ] ξ), ?_, hconst⟩
  exact L.centralizer_mem_pairingLeviSpan_descent_tmul ξ

end Langlands.Geometry.Building
