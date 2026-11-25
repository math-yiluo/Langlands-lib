/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
/-!
# Full subcategories under scalar localization

Source: the Hom formula of `def-weil-rationalization-karoubi`.
(blueprint: lem-sf-scalar-localization-full-subcategory).
The inclusion applies the underlying full-subcategory Hom equivalence to the tensor factor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe r u v
open CategoryTheory TensorProduct
namespace CategoryTheory.ScalarLocalization
variable (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (P : ObjectProperty C) (p : R)
/-- The inherited linear Hom equivalence of a full subcategory.
Source: the raw rationalization Hom formula
(blueprint: lem-sf-scalar-localization-full-subcategory). -/
def fullSubcategoryHomEquiv (K M : P.FullSubcategory) :
    (K ⟶ M) ≃ₗ[R] (K.obj ⟶ M.obj) where
  toFun f := f.hom
  invFun f := ObjectProperty.homMk f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- The ambient inclusion after localizing scalars.
Source: the raw rationalization Hom formula
(blueprint: lem-sf-scalar-localization-full-subcategory). -/
noncomputable def fullSubcategoryInclusion : ScalarLocalization R P.FullSubcategory p ⥤
    ScalarLocalization R C p where
  obj K := ⟨K.obj.obj⟩
  map {K M} f :=
    TensorProduct.congr (LinearEquiv.refl R (Localization.Away p))
      (fullSubcategoryHomEquiv R C P K.obj M.obj) f
  map_id K := by
    change TensorProduct.congr _ _ ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 K.obj) = _
    rfl
  map_comp {K M N} f g := by
    change TensorProduct.congr _ _
        (composition R P.FullSubcategory p K.obj M.obj N.obj g f) =
      composition R C p K.obj.obj M.obj.obj N.obj.obj
        (TensorProduct.congr _ _ g) (TensorProduct.congr _ _ f)
    induction g using TensorProduct.inductionOn with
    | tmul b g =>
      induction f using TensorProduct.inductionOn with
      | tmul a f =>
        simp only [composition_tmul, TensorProduct.congr_tmul]
        rfl
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]
/-- Tensoring the inherited Hom equivalence proves full faithfulness.
Source: the raw rationalization Hom formula
(blueprint: lem-sf-scalar-localization-full-subcategory).
Proof: tensor the identity equivalence on localized coefficients with the underlying
Hom equivalence. Its inverse is the preimage map; the inverse laws are those of the
tensor-product linear equivalence. Composition follows on pure tensors from the
inherited composition, and tensor induction extends this to arbitrary morphisms. -/
noncomputable def fullyFaithfulFullSubcategoryInclusion :
    (fullSubcategoryInclusion R C P p).FullyFaithful where
  preimage {K M} f :=
    (TensorProduct.congr (LinearEquiv.refl R (Localization.Away p))
      (fullSubcategoryHomEquiv R C P K.obj M.obj)).symm f
  map_preimage f := LinearEquiv.apply_symm_apply _ f
  preimage_map f := LinearEquiv.symm_apply_apply _ f
end CategoryTheory.ScalarLocalization
