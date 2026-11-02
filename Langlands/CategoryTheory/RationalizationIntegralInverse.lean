import Langlands.CategoryTheory.RationalizationEquivariantDenominators

/-! # Integral inverse-multiple data and rational isomorphisms -/

noncomputable section

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 800000

universe v u w

namespace Langlands.Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Actual maps in both directions whose two composites are the same
nonzero integer multiple of the respective identities. -/
structure IntegralInverseData (X Y : C) where
  multiple : ℤ
  multiple_ne_zero : multiple ≠ 0
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv : hom ≫ inv = multiple • 𝟙 X
  inv_hom : inv ≫ hom = multiple • 𝟙 Y

namespace IntegralInverseData

variable {X Y : C}

/-- The rationalization of the forward integral map is invertible. -/
def toIso (d : IntegralInverseData X Y) : of X ≅ of Y where
  hom := ofHom d.hom
  inv := (d.multiple : ℚ)⁻¹ • ofHom d.inv
  hom_inv_id := by
    rw [Linear.comp_smul]
    change (d.multiple : ℚ)⁻¹ • comp X Y X (ofHom d.hom) (ofHom d.inv) =
      identity X
    rw [← ofHom_comp, d.hom_inv, map_zsmul, ofHom_id,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    have hn : (d.multiple : ℚ) ≠ 0 := by exact_mod_cast d.multiple_ne_zero
    rw [inv_mul_cancel₀ hn, one_smul]
    rfl
  inv_hom_id := by
    rw [Linear.smul_comp]
    change (d.multiple : ℚ)⁻¹ • comp Y X Y (ofHom d.inv) (ofHom d.hom) =
      identity Y
    rw [← ofHom_comp, d.inv_hom, map_zsmul, ofHom_id,
      ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    have hn : (d.multiple : ℚ) ≠ 0 := by exact_mod_cast d.multiple_ne_zero
    rw [inv_mul_cancel₀ hn, one_smul]
    rfl

@[simp] theorem toIso_hom (d : IntegralInverseData X Y) :
    d.toIso.hom = ofHom d.hom := rfl

@[simp] theorem toIso_inv (d : IntegralInverseData X Y) :
    d.toIso.inv = (d.multiple : ℚ)⁻¹ • ofHom d.inv := rfl

end IntegralInverseData

variable {O : Type w} [Ring O] {X Y : C}
    (a : O →+* CategoryTheory.End X) (a' : O →+* CategoryTheory.End Y)

/-- Integral inverse-multiple data with exact equivariance in both directions. -/
structure EquivariantIntegralInverseData extends IntegralInverseData X Y where
  hom_intertwines : ∀ x : O, a x ≫ hom = hom ≫ a' x
  inv_intertwines : ∀ x : O, a' x ≫ inv = inv ≫ a x

namespace EquivariantIntegralIsoData

variable {a a'} {e : of X ≅ of Y}

/-- Forget the particular rational isomorphism but retain its exact integral
maps, equivariance, and the nonzero product of the denominators. -/
def toInverseData (d : EquivariantIntegralIsoData a a' e) :
    EquivariantIntegralInverseData a a' where
  multiple := d.homDenom * d.invDenom
  multiple_ne_zero := mul_ne_zero d.homDenom_ne_zero d.invDenom_ne_zero
  hom := d.hom
  inv := d.inv
  hom_inv := d.hom_inv
  inv_hom := d.inv_hom
  hom_intertwines := d.hom_intertwines
  inv_intertwines := d.inv_intertwines

end EquivariantIntegralIsoData

end Langlands.Rationalization
