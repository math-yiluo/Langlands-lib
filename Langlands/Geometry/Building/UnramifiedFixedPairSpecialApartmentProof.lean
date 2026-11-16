import Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentStatement
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedBuildingPairRecovery
import Langlands.Geometry.Building.UnramifiedUnitFixedPairApartment

/-! # A common centralizing special apartment for two fixed points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.Geometry.Building

/-- Two coefficient-fixed, torus-unit-fixed points lie in one centralizing
translate of the supplied special apartment, with normalizer-valued
coefficient differences. -/
theorem unramifiedFixedPairSpecialApartment :
    UnramifiedFixedPairSpecialApartmentStatement.{u} := by
  intro F _ _ _ _ G hG S iS hS T iT f hf hiT D C hDC hD y₁ y₂ hy₁ hunit₁ hy₂ hunit₂
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  let M := recoveredFixedBuildingPairModels D hG hiT C hDC hD y₁ y₂ hy₁ hy₂
  let g := unitFixedPairApartmentOfNeutralModel iS iT D M.lower
    M.baseChange_full_integralPoints hG hS.isSplitSubtorus hiT C hDC f hf hunit₁ hunit₂
  exact ⟨g.val, g.property⟩

end Langlands.Geometry.Building
