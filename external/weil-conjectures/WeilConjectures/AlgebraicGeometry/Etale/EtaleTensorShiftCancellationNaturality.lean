/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels

/-! # Naturality of opposite-shift tensor cancellation

Source: Stacks Project, Tags 08JC and 08J9; blueprint `lemma-change-coefficients-internal-hom--1`,
proof paragraph 2. (blueprint: lem-coef-etale-tensor-shift-cancellation-naturality) -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
  _root_.DerivedCategory.instMonoidalCategory
  _root_.DerivedCategory.commShift₂CurriedTensor

private theorem three_squares {D : Type*} [Category D]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃)
    (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂) (c' : B₂ ⟶ B₃)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (f₂ : A₂ ⟶ B₂) (f₃ : A₃ ⟶ B₃)
    (h₁ : f₀ ≫ a' = a ≫ f₁) (h₂ : f₁ ≫ b' = b ≫ f₂)
    (h₃ : f₂ ≫ c' = c ≫ f₃) :
    f₀ ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ f₃ := by
  simp only [← Category.assoc]
  rw [h₁, Category.assoc a, h₂, Category.assoc a, Category.assoc b, h₃]
  simp only [Category.assoc]

private theorem cancellation_natural_aux
    {D : Type*} [Category D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (T : D ⥤ D ⥤ D) [T.CommShift₂Int]
    (K : D) {L L' : D} (g : L ⟶ L') (n : ℤ) :
    (T.obj (K⟦-n⟧)).map (g⟦n⟧') ≫
        ((T.flip.obj (L'⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((T.obj K).commShiftIso n).hom.app L')⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _ =
      (((T.flip.obj (L⟦n⟧)).commShiftIso (-n)).hom.app K ≫
        (((T.obj K).commShiftIso n).hom.app L)⟦-n⟧' ≫
        (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.app _) ≫
          (T.obj K).map g := by
  have h₁ := NatTrans.shift_app_comm (T.flip.map (g⟦n⟧')) (-n) K
  have h₂ := Functor.commShiftIso_hom_naturality (T.obj K) g n
  have h₃ := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality
    ((T.obj K).map g)
  simp only [Functor.flip_map_app] at h₁
  simp only [Functor.comp_map, Functor.id_map] at h₃
  have h₂' := congrArg ((shiftFunctor D (-n)).map) h₂
  simp only [Functor.map_comp] at h₂'
  exact three_squares _ _ _ _ _ _ _ _ _ _ h₁.symm h₂' h₃

/-- Tensor cancellation of two opposite shifts is natural in its second variable.
Source: Stacks Project, Tags 08JC and 08J9; the tensor-Hom shift diagram in
blueprint `lemma-change-coefficients-internal-hom--1`, proof paragraph 2.

Proof. The first tensor-shift square commutes because maps of the tensor bifunctor
commute with shifts. The second square is naturality of the other tensor shift,
shifted by `-n`. The final square is naturality of the cancellation isomorphism
from shifting by `n` and then `-n` to the identity. Compose these three squares.
(blueprint: lem-coef-etale-tensor-shift-cancellation-naturality) -/
theorem etaleHomTensorShiftCancellation_naturality
    (C : Type*) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C))
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)}
    (g : L ⟶ L') (n : ℤ) :
    ((derivedTensor C X).obj (K⟦-n⟧)).map (g⟦n⟧') ≫
        etaleHomTensorShiftCancellation C X K L' n =
      etaleHomTensorShiftCancellation C X K L n ≫
        ((derivedTensor C X).obj K).map g := by
  exact cancellation_natural_aux
    (curriedTensor (_root_.DerivedCategory (Sheaf X.smallEtaleTopology C))) K g n

end AlgebraicGeometry.Etale
