/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso

/-!
# Associativity of the identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`

The identifications `AlgebraicGeometry.Etale.shiftTateObjectAddIso` are associative with respect
to the associator of the derived tensor product. This follows from the associativity of the
twists (`HasTateTwist.twistObjectAddIso_assoc`) and the compatibility of the associator with the
shifts (`AlgebraicGeometry.Etale.derivedTensorShiftIso_assoc`).

## Main statements

- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_hom_assoc`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]
  (U : Scheme.{u}) [HasInvertibleExponent Λ U]

/-- The associativity of `Λ(m)[p] ⊗ Λ(m')[q] ≅ Λ(m + m')[p + q]` for arbitrary shifts. -/
lemma shiftTateObjectAddIso_assoc_aux (a b c p q r : ℤ) :
    derivedTensorHom (ModuleCat.{u + 1} Λ)
      ((derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U b) p q).hom ≫
        (HasTateTwist.twistObjectAddIso U a b).hom⟦p + q⟧') (𝟙 ((tateObject Λ U c)⟦r⟧)) ≫
      (derivedTensorShiftIso _ (tateObject Λ U (a + b)) (tateObject Λ U c) (p + q) r).hom ≫
      (HasTateTwist.twistObjectAddIso U (a + b) c).hom⟦p + q + r⟧' =
    (derivedTensorAssociator _ U _ _ _).hom ≫
      derivedTensorHom _ (𝟙 ((tateObject Λ U a)⟦p⟧))
        ((derivedTensorShiftIso _ (tateObject Λ U b) (tateObject Λ U c) q r).hom ≫
          (HasTateTwist.twistObjectAddIso U b c).hom⟦q + r⟧') ≫
      (derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U (b + c)) p (q + r)).hom ≫
      (HasTateTwist.twistObjectAddIso U a (b + c)).hom⟦p + (q + r)⟧' ≫
      eqToHom (by simp only [add_assoc]) := by
  have hT := HasTateTwist.twistObjectAddIso_assoc (Λ := Λ) U a b c
  have hD := derivedTensorShiftIso_assoc (ModuleCat.{u + 1} Λ) (tateObject Λ U a)
    (tateObject Λ U b) (tateObject Λ U c) p q r
  rw [← Category.comp_id (𝟙 ((tateObject Λ U c)⟦r⟧)), ← derivedTensorHom_comp]
  have hT' : derivedTensorHom (ModuleCat.{u + 1} Λ) (HasTateTwist.twistObjectAddIso U a b).hom
      (𝟙 (tateObject Λ U c)) ≫ (HasTateTwist.twistObjectAddIso U (a + b) c).hom =
      (derivedTensorAssociator _ U _ _ _).hom ≫
        derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 (tateObject Λ U a))
          (HasTateTwist.twistObjectAddIso U b c).hom ≫
        (HasTateTwist.twistObjectAddIso U a (b + c)).hom ≫ eqToHom (by rw [add_assoc]) := by
    simp only [derivedTensorHom, CategoryTheory.Functor.map_id, Category.comp_id,
      NatTrans.id_app, Category.id_comp]
    exact hT
  have hN₁ := derivedTensorHom_shift_comp_derivedTensorShiftIso_hom (ModuleCat.{u + 1} Λ)
    (HasTateTwist.twistObjectAddIso U a b).hom (𝟙 (tateObject Λ U c)) (p + q) r
  have hN₂ := derivedTensorHom_shift_comp_derivedTensorShiftIso_hom (ModuleCat.{u + 1} Λ)
    (𝟙 (tateObject Λ U a)) (HasTateTwist.twistObjectAddIso U b c).hom p (q + r)
  rw [CategoryTheory.Functor.map_id] at hN₁ hN₂
  rw [Category.assoc]
  erw [reassoc_of% hN₁]
  rw [← Functor.map_comp, hT', Functor.map_comp]
  erw [reassoc_of% hD]
  rw [← Category.comp_id (𝟙 ((tateObject Λ U a)⟦p⟧)), ← derivedTensorHom_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hN₂]
  have hE : ∀ {P Q : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (f : P ⟶ Q) {n n' : ℤ} (h : n = n'),
      (eqToHom (by rw [h]) : P⟦n⟧ ⟶ P⟦n'⟧) ≫ f⟦n'⟧' = f⟦n⟧' ≫ eqToHom (by rw [h]) := by
    intro P Q f n n' h
    subst h
    simp
  rw [Category.comp_id]
  erw [hE _ (show p + (q + r) = p + q + r by ring)]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  rfl


/-- `Λ(m) ⊗ Λ(m') ⟶ Λ(m + m')`, with source and target written with `tateObject`. -/
noncomputable def tateObjectAddHom (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (tateObject Λ U m)).obj (tateObject Λ U m') ⟶
      tateObject Λ U (m + m') :=
  (HasTateTwist.twistObjectAddIso U m m').hom

/-- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_assoc_aux` with `tateObjectAddHom`. -/
lemma shiftTateObjectAddIso_assoc_aux' (a b c p q r : ℤ) :
    derivedTensorHom (ModuleCat.{u + 1} Λ)
      ((derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U b) p q).hom ≫
        (tateObjectAddHom Λ U a b)⟦p + q⟧') (𝟙 ((tateObject Λ U c)⟦r⟧)) ≫
      (derivedTensorShiftIso _ (tateObject Λ U (a + b)) (tateObject Λ U c) (p + q) r).hom ≫
      (tateObjectAddHom Λ U (a + b) c)⟦p + q + r⟧' =
    (derivedTensorAssociator _ U _ _ _).hom ≫
      derivedTensorHom _ (𝟙 ((tateObject Λ U a)⟦p⟧))
        ((derivedTensorShiftIso _ (tateObject Λ U b) (tateObject Λ U c) q r).hom ≫
          (tateObjectAddHom Λ U b c)⟦q + r⟧') ≫
      (derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U (b + c)) p (q + r)).hom ≫
      (tateObjectAddHom Λ U a (b + c))⟦p + (q + r)⟧' ≫
      eqToHom (by simp only [add_assoc]) :=
  shiftTateObjectAddIso_assoc_aux Λ U a b c p q r

/-- Unfolding `AlgebraicGeometry.Etale.shiftTateObjectAddIso`. -/
lemma shiftTateObjectAddIso_hom_eq (m m' : ℤ) :
    (shiftTateObjectAddIso Λ U m m').hom =
      (derivedTensorShiftIso _ (tateObject Λ U m) (tateObject Λ U m') (2 * m) (2 * m')).hom ≫
        (tateObjectAddHom Λ U m m')⟦2 * m + 2 * m'⟧' ≫
        (eqToHom (by rw [mul_add]) : (tateObject Λ U (m + m'))⟦2 * m + 2 * m'⟧ ⟶
          (tateObject Λ U (m + m'))⟦2 * (m + m')⟧) := rfl

/-- The identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` are associative. -/
theorem shiftTateObjectAddIso_hom_assoc (a b c : ℤ) :
    derivedTensorHom (ModuleCat.{u + 1} Λ) (shiftTateObjectAddIso Λ U a b).hom
        (𝟙 ((tateObject Λ U c)⟦2 * c⟧)) ≫ (shiftTateObjectAddIso Λ U (a + b) c).hom =
      (derivedTensorAssociator _ U _ _ _).hom ≫
        derivedTensorHom _ (𝟙 ((tateObject Λ U a)⟦2 * a⟧)) (shiftTateObjectAddIso Λ U b c).hom ≫
          (shiftTateObjectAddIso Λ U a (b + c)).hom ≫ eqToHom (by rw [add_assoc]) := by
  have hk := shiftTateObjectAddIso_assoc_aux' Λ U a b c (2 * a) (2 * b) (2 * c)
  have hE : ∀ {P Q R : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (f : P ⟶ Q) {n n' : ℤ} (h : n = n') (g : Q⟦n'⟧ ⟶ R),
      (eqToHom (by rw [h]) : P⟦n⟧ ⟶ P⟦n'⟧) ≫ f⟦n'⟧' ≫ g = f⟦n⟧' ≫ eqToHom (by rw [h]) ≫ g := by
    intro P Q R f n n' h g
    subst h
    simp
  have e₁ := derivedTensorHom_comp_eqToHom_comp_derivedTensorShiftIso_hom (ModuleCat.{u + 1} Λ)
    (tateObject Λ U (a + b)) (tateObject Λ U c) (show 2 * a + 2 * b = 2 * (a + b) by ring)
    (2 * c) rfl ((derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U b) (2 * a)
      (2 * b)).hom ≫ (tateObjectAddHom Λ U a b)⟦2 * a + 2 * b⟧') (by rw [mul_add])
  have e₂ := derivedTensorHom_id_comp_eqToHom_comp_derivedTensorShiftIso_hom
    (ModuleCat.{u + 1} Λ) (tateObject Λ U a) (tateObject Λ U (b + c)) (2 * a)
    (show 2 * b + 2 * c = 2 * (b + c) by ring) rfl
    ((derivedTensorShiftIso _ (tateObject Λ U b) (tateObject Λ U c) (2 * b)
      (2 * c)).hom ≫ (tateObjectAddHom Λ U b c)⟦2 * b + 2 * c⟧') (by rw [mul_add])
  simp only [shiftTateObjectAddIso_hom_eq]
  rw [← Category.assoc (derivedTensorShiftIso _ _ _ (2 * a) (2 * b)).hom,
    ← Category.assoc (derivedTensorShiftIso _ _ _ (2 * b) (2 * c)).hom]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) e₁).trans ?_
  rw [← Category.assoc (derivedTensorHom _ (𝟙 _) _), ← Category.assoc (derivedTensorHom _ (𝟙 _) _)]
  rw [e₂]
  generalize derivedTensorHom (ModuleCat.{u + 1} Λ)
    ((derivedTensorShiftIso _ (tateObject Λ U a) (tateObject Λ U b) (2 * a) (2 * b)).hom ≫
      (tateObjectAddHom Λ U a b)⟦2 * a + 2 * b⟧') (𝟙 ((tateObject Λ U c)⟦2 * c⟧)) = d₁ at hk ⊢
  generalize derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 ((tateObject Λ U a)⟦2 * a⟧))
    ((derivedTensorShiftIso _ (tateObject Λ U b) (tateObject Λ U c) (2 * b) (2 * c)).hom ≫
      (tateObjectAddHom Λ U b c)⟦2 * b + 2 * c⟧') = d₂ at hk ⊢
  simp only [Category.assoc] at hk ⊢
  rw [hE _ (show 2 * a + 2 * b + 2 * c = 2 * (a + b) + 2 * c by ring),
    hE _ (show 2 * a + (2 * b + 2 * c) = 2 * a + 2 * (b + c) by ring), reassoc_of% hk]
  simp

end Etale

end AlgebraicGeometry
