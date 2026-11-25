/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Normalization formulas for a localized linear adjunction

Source: current blueprint, sk-prop-sp-rational-adjunction, the tensor-Hom chain and
its normalized unit and every-model Hom formula (blueprint: lem-sp-localized-adjunction-formulas).
-/

@[expose] public noncomputable section
set_option autoImplicit false

namespace CategoryTheory.Adjunction

open Category

variable {C₀ D₀ C D : Type*} [Category* C₀] [Category* D₀] [Category* C] [Category* D]
  {F₀ : C₀ ⥤ D₀} {J₀ : D₀ ⥤ C₀} {F : C ⥤ D} {J : D ⥤ C}
  (A₀ : F₀ ⊣ J₀) (A : F ⊣ J) (QX : C₀ ⥤ C) (QY : D₀ ⥤ D)
  (a : J₀ ⋙ QX ≅ QY ⋙ J) (b : F₀ ⋙ QY ≅ QX ⋙ F)

/-- On integral arrows the normalized unit determines the entire Hom comparison.
Source: the blueprint's middle tensor-Hom arrow.
Proof: express the transpose using the unit. Substitute its normalization, cancel
b against its inverse, use naturality of a, and combine QX's two maps.
(blueprint: lem-sp-localized-adjunction-formulas). -/
private theorem homEquiv_integral_of_unit
    (hu : ∀ M₀, A.unit.app (QX.obj M₀) =
      QX.map (A₀.unit.app M₀) ≫ a.hom.app _ ≫ J.map (b.hom.app M₀))
    {M₀ : C₀} {K₀ : D₀} (h : F₀.obj M₀ ⟶ K₀) :
    A.homEquiv (QX.obj M₀) (QY.obj K₀) (b.inv.app M₀ ≫ QY.map h) =
      QX.map (A₀.homEquiv M₀ K₀ h) ≫ a.hom.app K₀ := by
  rw [A.homEquiv_unit, hu, J.map_comp]
  simp only [assoc, ← J.map_comp_assoc, Iso.hom_inv_id_app]
  erw [J.map_id, id_comp]
  erw [← a.hom.naturality]
  simp only [Functor.comp_map, ← QX.map_comp_assoc, A₀.homEquiv_unit]

section Linear

variable {R : Type*} [Semiring R] [Preadditive C] [Preadditive D]
  [Linear R C] [Linear R D] [J.Linear R]

/-- Transposition is linear when the right adjoint is linear.
Source: naturality in constant scalars in the tensor-Hom chain.
Proof: transposition is unit followed by J applied to the arrow, so linearity of
J and bilinearity of composition give the equation.
(blueprint: lem-sp-localized-adjunction-formulas). -/
private theorem homEquiv_smul_of_right_linear {M : C} {K : D} (h : F.obj M ⟶ K) (r : R) :
    A.homEquiv M K (r • h) = r • A.homEquiv M K h := by
  simp only [A.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

/-- The pure-tensor formula is valid for every pair of model identifications.
Source: the three-arrow chain and independence of models in the blueprint.
Proof: naturality removes the model isomorphisms; move the scalar across b by
bilinearity, use linearity of transposition and the integral formula, then move
the scalar past a. Reinsert the two model isomorphisms.
(blueprint: lem-sp-localized-adjunction-formulas). -/
theorem homEquiv_model_of_unit
    (hu : ∀ M₀, A.unit.app (QX.obj M₀) =
      QX.map (A₀.unit.app M₀) ≫ a.hom.app _ ≫ J.map (b.hom.app M₀))
    {M₀ : C₀} {K₀ : D₀} {M : C} {K : D}
    (i : QX.obj M₀ ≅ M) (j : QY.obj K₀ ≅ K)
    (h : F₀.obj M₀ ⟶ K₀) (r : R) :
    A.homEquiv M K (F.map i.inv ≫ b.inv.app M₀ ≫ (r • QY.map h) ≫ j.hom) =
      i.inv ≫ (r • QX.map (A₀.homEquiv M₀ K₀ h)) ≫ a.hom.app K₀ ≫ J.map j.hom := by
  have hs : A.homEquiv (QX.obj M₀) (QY.obj K₀)
      (b.inv.app M₀ ≫ (r • QY.map h)) =
      (r • QX.map (A₀.homEquiv M₀ K₀ h)) ≫ a.hom.app K₀ := by
    rw [Linear.comp_smul, A.homEquiv_smul_of_right_linear,
      homEquiv_integral_of_unit A₀ A QX QY a b hu, ← Linear.smul_comp]
  rw [A.homEquiv_naturality_left]
  rw [← assoc (b.inv.app M₀), A.homEquiv_naturality_right, hs]
  simp only [assoc]

end Linear

end CategoryTheory.Adjunction
