/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar

/-! # Closed-support comparison for Cartier classes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The specified supported-source mate is invertible.
Source: blueprint lemma-cycle-class-cartier-divisor, opening comparison paragraph
(blueprint: lem-sfb-geo-cartier-source-comparison).
Proof: a closed immersion is qcqs. Its ordinary discrete direct-image comparison
is an isomorphism. Compose its component with direct image of the constant-sheaf
comparison isomorphism, exactly as in the definition of the specified mate. -/
instance geoCartierSourceComparison_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] :
    IsIso (geoCartierSourceComparison A i) := by
  let := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  unfold geoCartierSourceComparison
  change IsIso
    (((asIso (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A))).app
      (Etale.ordinaryFiniteConstant A D) ≪≫
        (lowerStar (ModuleCat.{u + 1} A) i).mapIso
          ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A))).hom)
  infer_instance

end AlgebraicGeometry.ProEtale
