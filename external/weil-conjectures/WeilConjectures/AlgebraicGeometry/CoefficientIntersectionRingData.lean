/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Ring maps on coefficient intersections

Source: Stacks Project, Tags 0097, 01I9 and 02KG.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The lift of the base-change square to the inverse image of the base open. 
(blueprint: def-pc-coefficient-intersection-ring-data)
-/
def coefficientRestrictedLift {X T T' X' : Scheme.{u}}
    (f : X ⟶ T) (U : T.Opens) (g : T' ⟶ U.toScheme)
    (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι)) : X' ⟶ (f ⁻¹ᵁ U).toScheme :=
  ((isPullback_morphismRestrict f U).flip).lift g' (f' ≫ g)
    (by rw [sq.w, Category.assoc])

/-- The inverse-image coefficient intersection lies over its original coefficient open. 
(blueprint: def-pc-coefficient-intersection-ring-data)
-/
theorem coefficientIntersection_le {X T T' X' : Scheme.{u}}
    (f : X ⟶ T) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) (B : T'.Opens) :
    W ⊓ f' ⁻¹ᵁ B ≤ coefficientRestrictedLift f U g g' f' sq ⁻¹ᵁ Z := by
  have hk : coefficientRestrictedLift f U g g' f' sq ≫ (f ⁻¹ᵁ U).ι = g' :=
    ((isPullback_morphismRestrict f U).flip).lift_fst _ _ _
  have he : coefficientRestrictedLift f U g g' f' sq ⁻¹ᵁ Z = W := by
    rw [hW]
    conv_rhs => rw [← hk]
    change _ = coefficientRestrictedLift f U g g' f' sq ⁻¹ᵁ
      ((f ⁻¹ᵁ U).ι ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    rw [Scheme.Hom.preimage_image_eq]
  rw [he]
  exact inf_le_left

/-- Structural map from the affine base ring to the coefficient ring. 
(blueprint: def-pc-coefficient-intersection-ring-data)
-/
def coefficientBaseRingMap {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) : Γ(U.toScheme, ⊤) →+* Γ((f ⁻¹ᵁ U).toScheme, Z) :=
  ((f ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE le_top).op).hom.comp
    (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
      ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)

/-- Structural map from the coefficient ring to the intersection ring.
Source: Stacks Project, Tags 0097 and 02KG.
(blueprint: def-pc-coefficient-intersection-ring-data). -/
def coefficientIntersectionRingMap {X T T' X' : Scheme.{u}}
    (f : X ⟶ T) (U : T.Opens) (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)) (B : T'.Opens) :
    Γ((f ⁻¹ᵁ U).toScheme, Z) →+* Γ(X', W ⊓ f' ⁻¹ᵁ B) :=
  ((coefficientRestrictedLift f U g g' f' sq).appLE Z (W ⊓ f' ⁻¹ᵁ B)
    (coefficientIntersection_le f U Z g g' f' sq W hW B)).hom

end
end AlgebraicGeometry.Scheme.Modules
