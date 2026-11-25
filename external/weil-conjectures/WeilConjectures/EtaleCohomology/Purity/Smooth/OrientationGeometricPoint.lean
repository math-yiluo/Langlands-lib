/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation

/-!
# The global orientation at the geometric points

With the Tate twist `Λ(1) = μₙ ⊗ Λ`, let `pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` be the global
orientation of the zero section `s` of `𝔸¹_Y`, the adjoint of the Kummer boundary `∂κ(t)`
(`AlgebraicGeometry.Etale.affineLineOrientation`). For a geometric point `ȳ : Spec Ω ⟶ Y`
(`Ω` algebraically closed), the restriction of `pur_s` along the base change
`𝔸¹_ȳ : 𝔸¹_Ω ⟶ 𝔸¹_Y` is the normalized class `1 ∈ H²_{s(ȳ)}(𝔸¹_Ω, Λ(1))` of the rank-one local
calculation (`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv`). This is the
last clause of blueprint `thm-pur-affine-line-orientation`.

## Main statements

- `Etale.supportCohomologyAffineLineLinearEquiv_restrictSupportedClass_kummerBoundary`
- `Etale.supportCohomologyAffineLineLinearEquiv_restrictAffineLineZeroLocusHom`
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] neZero_ringChar_of_finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {Y : Scheme.{u}} [HasInvertibleExponent Λ Y]
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]
  (y : Spec (.of Ω) ⟶ Y)

set_option maxRecDepth 4000 in
-- rewriting inside the derived-category terms of the statement is deep
/-- Blueprint `thm-pur-affine-line-orientation`: Global orientation and its normalization (the
normalization at the geometric points, for classes with supports).

For a geometric point `ȳ : Spec Ω ⟶ Y`, the restriction of the Kummer boundary
`∂κ(t) ∈ H²_{s(Y)}(𝔸¹_Y, Λ(1))` along the base change `𝔸¹_ȳ : 𝔸¹_Ω ⟶ 𝔸¹_Y` of the zero section
pair (`AlgebraicGeometry.Etale.restrictSupportedClass`), read in `H²_{s(ȳ)}(𝔸¹_Ω, Λ(1))`, is
sent to `1` by the normalized isomorphism `H²_{s(ȳ)}(𝔸¹_Ω, Λ(1)) ≅ Λ` of
`example-closed-support`
(`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv`): the restricted class is the
Kummer boundary of the coordinate of `𝔸¹_Ω`
(`AlgebraicGeometry.Etale.supportedClassMap_restrictSupportedClass_affineLineOrientation`). -/
theorem supportCohomologyAffineLineLinearEquiv_restrictSupportedClass_kummerBoundary :
    supportCohomologyAffineLineLinearEquiv Λ Ω ((supportCohomologyAddEquiv Λ _ _ 2).symm
      (supportedClassMap Λ _
        (restrictSupportedClass Λ (AffineSpace.map (ULift.{u} (Fin 1)) y) _ _
          _ (isPullback_zeroLocusSubschemeι_coord y)
          (leftDerivedUpperStarConstantComplexIso Λ (AffineSpace.map (ULift.{u} (Fin 1)) y)).inv
          (((L((AffineSpace.map (ULift.{u} (Fin 1)) y)^*[ModuleCat.{u + 1} Λ])).commShiftIso
              (2 : ℤ)).app _ ≪≫
            (shiftFunctor _ (2 : ℤ)).mapIso
              (leftDerivedUpperStarTateObjectIso (AffineSpace.map (ULift.{u} (Fin 1)) y) 1))
          (shiftSupportedClass Λ _ 2
            (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0))))))) = 1 := by
  rw [supportedClassMap_restrictSupportedClass_affineLineOrientation Λ y]
  exact supportCohomologyAffineLineLinearEquiv_kummerBoundary Λ Ω

set_option maxRecDepth 4000 in
-- rewriting inside the derived-category terms of the statement is deep
/-- Blueprint `thm-pur-affine-line-orientation`: Global orientation and its normalization (the
normalization at the geometric points).

For a geometric point `ȳ : Spec Ω ⟶ Y` (`Ω` algebraically closed), the restriction of the global
orientation `pur_s : Λ_{V(t)} ⟶ Rs^! Λ(1)[2]` along the base change `𝔸¹_ȳ : 𝔸¹_Ω ⟶ 𝔸¹_Y`
(`AlgebraicGeometry.Etale.restrictAffineLineZeroLocusHom`, the exceptional base change applied
to the pullback of `pur_s`), read as a class in `H²_{s(ȳ)}(𝔸¹_Ω, Λ(1))`
(`AlgebraicGeometry.Etale.supportCohomologyAddEquiv`), is the normalized class `1` of
`example-closed-support`: the isomorphism
`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv` sends it to `1`. Indeed the
restriction of `pur_s` is the orientation over `Spec Ω`
(`AlgebraicGeometry.Etale.restrictAffineLineZeroLocusHom_affineLineOrientation`: the Kummer
class and the boundary of the localization triangle are compatible with base change), i.e. the
adjoint of the Kummer boundary of the coordinate of `𝔸¹_Ω`, which is sent to `1`
(`AlgebraicGeometry.Etale.supportCohomologyAffineLineLinearEquiv_kummerBoundary`). That `pur_s`
is an isomorphism is
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_isAlgClosed`. -/
theorem supportCohomologyAffineLineLinearEquiv_restrictAffineLineZeroLocusHom :
    supportCohomologyAffineLineLinearEquiv Λ Ω ((supportCohomologyAddEquiv Λ _ _ 2).symm
      (restrictAffineLineZeroLocusHom Λ y (affineLineOrientation Λ Y))) = 1 := by
  rw [restrictAffineLineZeroLocusHom_affineLineOrientation Λ y]
  exact supportCohomologyAffineLineLinearEquiv_kummerBoundary Λ Ω

end Etale

end AlgebraicGeometry
