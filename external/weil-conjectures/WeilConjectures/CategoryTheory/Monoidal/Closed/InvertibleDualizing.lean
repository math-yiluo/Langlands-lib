/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality

/-!
# Duality into an invertible object

Let `C` be a monoidal closed category, `T` an invertible object and `γ : T ≅ W` an isomorphism.
The contravariant functor `[-, W]` is then the coefficient dual `[-, 𝟙_ C]` twisted by `T`:
```
  θ_X : [X, W] ≅ [X, T] ≅ [X, 𝟙_ C ⊗ T] ≅ [X, 𝟙_ C] ⊗ T,
```
the first arrow being `[X, γ⁻¹]` and the last the inverse of the canonical map
`[X, 𝟙_ C] ⊗ T ⟶ [X, 𝟙_ C ⊗ T]`, an isomorphism since `T` is invertible
(`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`). This is the formal core of the
blueprint theorem `theorem-poincare-duality--2`: an orientation `γ : Λ_X(d)[2d] ≅ ω_X` identifies
the Verdier dual `𝔻_X = RHom(-, ω_X)` with `K ↦ K^∨(d)[2d]`.

If `C` is moreover braided, the double-dual map `X ⟶ [[X, W], W]` is identified, under `θ`, with
the coefficient biduality `X ⟶ [[X, 𝟙_ C], 𝟙_ C]`. Hence it is an isomorphism for every
dualizable `X`, and `[-, W]` restricts to an anti-equivalence of the dualizable objects.

## Main definitions

- `CategoryTheory.MonoidalClosed.ihomIsoIhomUnitTensor`: `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T`.
- `CategoryTheory.MonoidalClosed.ihomFlipIsoIhomUnitTensor`: `θ` as a natural isomorphism
  `[-, W] ≅ [-, 𝟙_ C] ⊗ T`.
- `CategoryTheory.MonoidalClosed.ihomUnitToIhomTensor`: the isomorphism
  `[A, 𝟙_ C] ⟶ [A ⊗ T, T]` for an invertible `T`.
- `CategoryTheory.MonoidalClosed.ihomIhomIsoIhomIhomUnit`: the isomorphism
  `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by `θ_X`.
- `CategoryTheory.MonoidalClosed.dualizableIhomEquivalence`: the anti-equivalence of the
  dualizable objects given by `[-, W]`.
- `CategoryTheory.MonoidalClosed.ihomUnitComparison`: the comparison `F [X, 𝟙_ C] ⟶ [F X, 𝟙_ D]`
  of coefficient duals along a monoidal functor `F`.

## Main statements

- `CategoryTheory.MonoidalClosed.whiskerLeft_ihomIsoIhomUnitTensor_hom_comp`: `θ` is compatible
  with the evaluations `X ⊗ [X, W] ⟶ W` and `X ⊗ [X, 𝟙_ C] ⟶ 𝟙_ C`.
- `CategoryTheory.MonoidalClosed.ihomCurry_comp_map_ihomIsoIhomUnitTensor_hom`: `θ` is compatible
  with internal currying, `[K ⊗ A, W] ≅ [A, [K, W]]`; this gives the compatibility with shifts.
- `CategoryTheory.MonoidalClosed.map_ihomIsoIhomUnitTensor_hom`: `θ` is compatible with monoidal
  functors, such as a change of coefficients (blueprint `theorem-poincare-duality--2`).
- `CategoryTheory.MonoidalClosed.toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom`: under `θ` the
  double-dual map into `[[X, W], W]` is the coefficient biduality.
- `CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_isDualizable`: biduality relative to `W`
  holds for every dualizable object.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory Opposite

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

section Twist

variable {T W : C} (γ : T ≅ W) (hT : IsInvertible T)

/-- Duality into an object `W` isomorphic to an invertible object `T` is the coefficient dual
twisted by `T`:
```
  θ_X : [X, W] ≅ [X, T] ≅ [X, 𝟙_ C ⊗ T] ≅ [X, 𝟙_ C] ⊗ T,
```
the composite of `[X, γ⁻¹]`, of the left unitor and of the inverse of the canonical map
`[X, 𝟙_ C] ⊗ T ⟶ [X, 𝟙_ C ⊗ T]` (`CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`). -/
noncomputable def ihomIsoIhomUnitTensor (X : C) : (ihom X).obj W ≅ (ihom X).obj (𝟙_ C) ⊗ T :=
  haveI := isIso_ihomTensorToIhom X (𝟙_ C) hT
  (ihom X).mapIso γ.symm ≪≫ (ihom X).mapIso (λ_ T).symm ≪≫
    (asIso (ihomTensorToIhom X (𝟙_ C) T)).symm

lemma ihomIsoIhomUnitTensor_inv (X : C) :
    (ihomIsoIhomUnitTensor γ hT X).inv =
      ihomTensorToIhom X (𝟙_ C) T ≫ (ihom X).map (λ_ T).hom ≫ (ihom X).map γ.hom := by
  simp [ihomIsoIhomUnitTensor]

/-- The isomorphism `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` is natural in `X`. -/
@[reassoc]
lemma pre_app_comp_ihomIsoIhomUnitTensor_hom {X Y : C} (f : X ⟶ Y) :
    (pre f).app W ≫ (ihomIsoIhomUnitTensor γ hT X).hom =
      (ihomIsoIhomUnitTensor γ hT Y).hom ≫ (pre f).app (𝟙_ C) ▷ T := by
  rw [← cancel_epi (ihomIsoIhomUnitTensor γ hT Y).inv, Iso.inv_hom_id_assoc,
    ← cancel_mono (ihomIsoIhomUnitTensor γ hT X).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ihomIsoIhomUnitTensor_inv, ihomIsoIhomUnitTensor_inv,
    pre_app_whiskerRight_comp_ihomTensorToIhom_assoc]
  simp only [Category.assoc, NatTrans.naturality, NatTrans.naturality_assoc]

/-- Duality into an object `W` isomorphic to an invertible object `T` is the coefficient dual
twisted by `T`: the natural isomorphism `θ : [-, W] ≅ [-, 𝟙_ C] ⊗ T` of contravariant functors
with components `CategoryTheory.MonoidalClosed.ihomIsoIhomUnitTensor`. -/
noncomputable def ihomFlipIsoIhomUnitTensor :
    internalHom.flip.obj W ≅ internalHom.flip.obj (𝟙_ C) ⋙ tensorRight T :=
  NatIso.ofComponents (fun X ↦ ihomIsoIhomUnitTensor γ hT X.unop)
    (fun f ↦ pre_app_comp_ihomIsoIhomUnitTensor_hom γ hT f.unop)

@[simp]
lemma ihomFlipIsoIhomUnitTensor_app (X : Cᵒᵖ) :
    (ihomFlipIsoIhomUnitTensor γ hT).app X = ihomIsoIhomUnitTensor γ hT X.unop :=
  rfl

/-- The isomorphism `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` is compatible with the evaluations: the
square
```
  X ⊗ [X, W] ────── X ◁ θ_X ──────→ X ⊗ ([X, 𝟙_ C] ⊗ T)
       │                                   │
       ev                         α⁻¹, ev ▷ T, λ
       ↓                                   ↓
       W ─────────────── γ⁻¹ ─────────────→ T
```
commutes. -/
@[reassoc]
lemma whiskerLeft_ihomIsoIhomUnitTensor_hom_comp (X : C) :
    X ◁ (ihomIsoIhomUnitTensor γ hT X).hom ≫ (α_ _ _ _).inv ≫
        (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom =
      (ihom.ev X).app W ≫ γ.inv := by
  rw [← reassoc_of% (whiskerLeft_ihomTensorToIhom_ev X (𝟙_ C) T),
    ← MonoidalCategory.whiskerLeft_comp_assoc]
  have : (ihomIsoIhomUnitTensor γ hT X).hom ≫ ihomTensorToIhom X (𝟙_ C) T =
      (ihom X).map γ.inv ≫ (ihom X).map (λ_ T).inv := by
    simp [ihomIsoIhomUnitTensor]
  rw [this, MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality_assoc,
    ihom.ev_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (compatibility with
twisting the source).

The isomorphism `θ` is compatible with internal currying: for all `K` and `A`, the square
```
  [K ⊗ A, W] ────────────────── θ_{K ⊗ A} ──────────────────→ [K ⊗ A, 𝟙_ C] ⊗ T
       │                                                              │
   ihomCurry                                                 ihomCurry ▷ T
       ↓                                                              ↓
  [A, [K, W]] ── [A, θ_K] ──→ [A, [K, 𝟙_ C] ⊗ T] ←── ihomTensorToIhom ── [A, [K, 𝟙_ C]] ⊗ T
```
commutes. For `A = Λ_X⟦n⟧` this is the compatibility of `θ` with shifts. -/
lemma ihomCurry_comp_map_ihomIsoIhomUnitTensor_hom (K A : C) :
    ihomCurry K A W ≫ (ihom A).map (ihomIsoIhomUnitTensor γ hT K).hom =
      (ihomIsoIhomUnitTensor γ hT (K ⊗ A)).hom ≫ ihomCurry K A (𝟙_ C) ▷ T ≫
        ihomTensorToIhom A ((ihom K).obj (𝟙_ C)) T := by
  rw [← cancel_epi (ihomIsoIhomUnitTensor γ hT (K ⊗ A)).inv, Iso.inv_hom_id_assoc,
    ← cancel_mono ((ihom A).map (ihomIsoIhomUnitTensor γ hT K).inv), Category.assoc,
    Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id, Category.comp_id,
    Category.assoc,
    ihomIsoIhomUnitTensor_inv, ihomIsoIhomUnitTensor_inv, Category.assoc, Category.assoc,
    map_comp_ihomCurry, map_comp_ihomCurry_assoc, ihomTensorToIhom_comp_ihomCurry_assoc]
  simp only [Functor.map_comp]

/-- The compatibility of `θ_X` with the evaluations, read along `θ_X⁻¹`. -/
@[reassoc]
lemma whiskerLeft_ihomIsoIhomUnitTensor_inv_comp (X : C) :
    X ◁ (ihomIsoIhomUnitTensor γ hT X).inv ≫ (ihom.ev X).app W ≫ γ.inv =
      (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom := by
  rw [← whiskerLeft_ihomIsoIhomUnitTensor_hom_comp γ hT X,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    Category.id_comp]

end Twist

section Functor

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {D : Type*} [Category* D] [MonoidalCategory D] [MonoidalClosed D] (F : C ⥤ D)
  [F.Monoidal]

/-- The comparison `F [X, 𝟙_ C] ⟶ [F X, 𝟙_ D]` of coefficient duals along a monoidal functor:
the comparison map `F [X, 𝟙_ C] ⟶ [F X, F 𝟙_ C]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) followed by `F 𝟙_ C ≅ 𝟙_ D`. -/
noncomputable def ihomUnitComparison (X : C) :
    F.obj ((ihom X).obj (𝟙_ C)) ⟶ (ihom (F.obj X)).obj (𝟙_ D) :=
  (ihomComparison F X).app (𝟙_ C) ≫ (ihom (F.obj X)).map (η F)

variable {T W : C} (γ : T ≅ W) (hT : IsInvertible T) {T' W' : D} (γ' : T' ≅ W')
  (hT' : IsInvertible T') (e : F.obj T ≅ T') (eW : F.obj W ≅ W')

/-- Blueprint `theorem-poincare-duality--2`: The dual of a perfect complex (compatibility with
finite reduction and scalar extension).

The twist interchange `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` is compatible with a monoidal functor
`F` (for instance a change of coefficients: finite reduction or extension of scalars), given
compatible identifications `F T ≅ T'` and `F W ≅ W'`: the square
```
  F [X, W] ──────────── F θ_X ───────────→ F ([X, 𝟙_ C] ⊗ T) ≅ F [X, 𝟙_ C] ⊗ F T
     │                                                    │
  comparison, e_W                              comparison ⊗ e
     ↓                                                    ↓
  [F X, W'] ─────────── θ'_{F X} ──────────────→ [F X, 𝟙_ D] ⊗ T'
```
commutes.

This is only the formal core of the change-of-coefficients clause: it is not yet instantiated
for finite reduction `Λ → Λ/ℓ^n` or extension of scalars on derived étale categories, and the
compatibility of `θ` with shifts under a change of coefficients is not yet stated. Both remain
to be done before the change-of-coefficients clause of `theorem-poincare-duality--2` is complete. -/
lemma map_ihomIsoIhomUnitTensor_hom (h : F.map γ.hom ≫ eW.hom = e.hom ≫ γ'.hom) (X : C) :
    F.map (ihomIsoIhomUnitTensor γ hT X).hom ≫ δ F _ _ ≫ (ihomUnitComparison F X ⊗ₘ e.hom) =
      (ihomComparison F X).app W ≫ (ihom (F.obj X)).map eW.hom ≫
        (ihomIsoIhomUnitTensor γ' hT' (F.obj X)).hom := by
  have core : F.obj X ◁ μ F _ T ≫ μ F X _ ≫
      F.map ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom) =
        (α_ _ _ _).inv ≫ (F.obj X ◁ ihomUnitComparison F X ≫ (ihom.ev (F.obj X)).app (𝟙_ D)) ▷
          F.obj T ≫ (λ_ _).hom := by
    simp only [Functor.map_comp, Functor.Monoidal.map_associator_inv,
      Functor.Monoidal.map_whiskerRight, Functor.Monoidal.map_leftUnitor, Category.assoc,
      Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.whiskerLeft_μ_δ_assoc, ihomUnitComparison,
      MonoidalCategory.whiskerLeft_comp_assoc, ihom.ev_naturality, ihomComparison_ev_assoc,
      comp_whiskerRight]
    erw [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ_assoc]
  have key : μ F _ _ ≫ F.map (ihomIsoIhomUnitTensor γ hT X).inv ≫
      (ihomComparison F X).app W ≫ (ihom (F.obj X)).map eW.hom =
        (ihomUnitComparison F X ⊗ₘ e.hom) ≫ (ihomIsoIhomUnitTensor γ' hT' (F.obj X)).inv := by
    apply uncurry_injective
    have h₁ : X ◁ (ihomIsoIhomUnitTensor γ hT X).inv ≫ (ihom.ev X).app W =
        ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ T ≫ (λ_ T).hom) ≫ γ.hom := by
      rw [← Iso.comp_inv_eq, Category.assoc, whiskerLeft_ihomIsoIhomUnitTensor_inv_comp]
    have h₂ : F.obj X ◁ (ihomIsoIhomUnitTensor γ' hT' (F.obj X)).inv ≫
        (ihom.ev (F.obj X)).app W' =
        ((α_ _ _ _).inv ≫ (ihom.ev (F.obj X)).app (𝟙_ D) ▷ T' ≫ (λ_ T').hom) ≫ γ'.hom := by
      rw [← Iso.comp_inv_eq, Category.assoc, whiskerLeft_ihomIsoIhomUnitTensor_inv_comp]
    rw [uncurry_eq, uncurry_eq]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [h₂, ihom.ev_naturality, ihomComparison_ev_assoc, μ_natural_right_assoc,
      ← F.map_comp_assoc, h₁, F.map_comp_assoc, h]
    rw [reassoc_of% core]
    simp only [tensorHom_def, MonoidalCategory.whiskerLeft_comp, Category.assoc, comp_whiskerRight]
    rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
      whisker_exchange_assoc]
    dsimp only [Functor.id_obj]
    rw [leftUnitor_naturality_assoc]
  rw [← cancel_mono (ihomIsoIhomUnitTensor γ' hT' (F.obj X)).inv, Category.assoc,
    Category.assoc, ← key, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Functor.Monoidal.δ_μ_assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
    Category.id_comp]

end Functor

section Braided

variable [BraidedCategory C]

/-- The map `[A, 𝟙_ C] ⟶ [A ⊗ T, T]`: the transpose of
```
                α, A ◁ β, α⁻¹                     ev ▷ T              λ
  (A ⊗ T) ⊗ [A, 𝟙_ C] ──────────→ (A ⊗ [A, 𝟙_ C]) ⊗ T ──────→ 𝟙_ C ⊗ T ──→ T.
```
It is an isomorphism for an invertible `T`
(`CategoryTheory.MonoidalClosed.isIso_ihomUnitToIhomTensor`). -/
noncomputable def ihomUnitToIhomTensor (A T : C) :
    (ihom A).obj (𝟙_ C) ⟶ (ihom (A ⊗ T)).obj T :=
  curry ((α_ A T _).hom ≫ A ◁ (β_ T _).hom ≫ (α_ A _ T).inv ≫
    (ihom.ev A).app (𝟙_ C) ▷ T ≫ (λ_ T).hom)

lemma uncurry_comp_ihomUnitToIhomTensor {A T Z : C} (x : Z ⟶ (ihom A).obj (𝟙_ C)) :
    uncurry (x ≫ ihomUnitToIhomTensor A T) =
      (α_ A T Z).hom ≫ A ◁ (β_ T Z).hom ≫ (α_ A Z T).inv ≫ uncurry x ▷ T ≫ (λ_ T).hom := by
  rw [uncurry_natural_left, ihomUnitToIhomTensor, uncurry_curry, uncurry_eq x,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    BraidedCategory.braiding_naturality_right, MonoidalCategory.whiskerLeft_comp_assoc,
    associator_inv_naturality_middle_assoc, comp_whiskerRight_assoc]

/-- For an invertible `T` the map `[A, 𝟙_ C] ⟶ [A ⊗ T, T]` is an isomorphism: both sides
corepresent `Z ↦ (A ⊗ Z ⟶ 𝟙_ C)`, since `- ⊗ T` is an autoequivalence. -/
theorem isIso_ihomUnitToIhomTensor (A : C) {T : C} (hT : IsInvertible T) :
    IsIso (ihomUnitToIhomTensor A T) := by
  obtain ⟨T', ⟨e⟩, ⟨e'⟩⟩ := hT
  let E := tensorRightEquivalenceOfTensorIso e e'
  let ι (Z : C) : (A ⊗ T) ⊗ Z ≅ (A ⊗ Z) ⊗ T :=
    α_ A T Z ≪≫ whiskerLeftIso A (β_ T Z) ≪≫ (α_ A Z T).symm
  have key {Z : C} (x : Z ⟶ (ihom A).obj (𝟙_ C)) :
      uncurry (x ≫ ihomUnitToIhomTensor A T) = (ι Z).hom ≫ uncurry x ▷ T ≫ (λ_ T).hom := by
    rw [uncurry_comp_ihomUnitToIhomTensor]
    simp [ι]
  refine isIso_of_yoneda_map_bijective _ (fun Z ↦ ⟨fun x x' h ↦ ?_, fun g ↦ ?_⟩)
  · have h' := congrArg uncurry h
    dsimp only at h'
    rw [key, key, cancel_epi, cancel_mono] at h'
    exact uncurry_injective (whiskerRight_injective_of_tensorIso e h')
  · let b : A ⊗ Z ⟶ 𝟙_ C := E.functor.preimage ((ι Z).inv ≫ uncurry g ≫ (λ_ T).inv)
    have hb : b ▷ T = (ι Z).inv ≫ uncurry g ≫ (λ_ T).inv := E.functor.map_preimage _
    refine ⟨curry b, uncurry_injective ?_⟩
    dsimp only
    rw [key, uncurry_curry, hb]
    simp

variable {T W : C} (γ : T ≅ W) (hT : IsInvertible T)

/-- Under `θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T` the double-dual map into `[[X, W], W]` is the
coefficient biduality: the square
```
         X ────────────── toIhomIhomUnit X ──────────────→ [[X, 𝟙_ C], 𝟙_ C]
         │                                                          │
  toIhomIhom W X                                    ihomUnitToIhomTensor _ T
         ↓                                                          ↓
  [[X, W], W] ── [θ_X⁻¹, W] ──→ [[X, 𝟙_ C] ⊗ T, W] ── [_, γ⁻¹] ──→ [[X, 𝟙_ C] ⊗ T, T]
```
commutes. -/
@[reassoc]
lemma toIhomIhom_comp_pre_app_comp_map (X : C) :
    toIhomIhom W X ≫ (pre (ihomIsoIhomUnitTensor γ hT X).inv).app W ≫
        (ihom ((ihom X).obj (𝟙_ C) ⊗ T)).map γ.inv =
      toIhomIhomUnit X ≫ ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) T := by
  apply uncurry_injective
  rw [← Category.assoc, uncurry_natural_right, uncurry_pre_app, uncurry_toIhomIhom,
    uncurry_comp_ihomUnitToIhomTensor,
    ← toIhomIhom_unit, uncurry_toIhomIhom, Category.assoc, Category.assoc,
    BraidedCategory.braiding_naturality_left_assoc, whiskerLeft_ihomIsoIhomUnitTensor_inv_comp,
    BraidedCategory.braiding_tensor_left_hom]
  simp

/-- The isomorphism `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by
`θ_X : [X, W] ≅ [X, 𝟙_ C] ⊗ T`:
```
  [[X, W], W] ≅ [[X, 𝟙_ C] ⊗ T, W] ≅ [[X, 𝟙_ C] ⊗ T, T] ≅ [[X, 𝟙_ C], 𝟙_ C],
```
the composite of `[θ_X⁻¹, W]`, of `[_, γ⁻¹]` and of the inverse of
`CategoryTheory.MonoidalClosed.ihomUnitToIhomTensor`. -/
noncomputable def ihomIhomIsoIhomIhomUnit (X : C) :
    (ihom ((ihom X).obj W)).obj W ≅ (ihom ((ihom X).obj (𝟙_ C))).obj (𝟙_ C) :=
  haveI := isIso_ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) hT
  ((internalHom.flip.obj W).mapIso (ihomIsoIhomUnitTensor γ hT X).op).symm ≪≫
    (ihom _).mapIso γ.symm ≪≫ (asIso (ihomUnitToIhomTensor ((ihom X).obj (𝟙_ C)) T)).symm

/-- Under the isomorphism `[[X, W], W] ≅ [[X, 𝟙_ C], 𝟙_ C]` induced by `θ_X`, the double-dual
map `X ⟶ [[X, W], W]` is the coefficient biduality `X ⟶ [[X, 𝟙_ C], 𝟙_ C]`. -/
@[reassoc (attr := simp)]
lemma toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom (X : C) :
    toIhomIhom W X ≫ (ihomIhomIsoIhomIhomUnit γ hT X).hom = toIhomIhomUnit X := by
  have h := toIhomIhom_comp_pre_app_comp_map γ hT X
  simp only [ihomIhomIsoIhomIhomUnit, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.op_inv]
  change toIhomIhom W X ≫ (pre (ihomIsoIhomUnitTensor γ hT X).inv).app W ≫ _ ≫ _ = _
  rw [reassoc_of% h]
  simp

include γ hT in
/-- Duality into an object `W` isomorphic to an invertible object `T` preserves dualizable
objects: `[X, W] ≅ [X, 𝟙_ C] ⊗ T` is dualizable for a dualizable `X`. -/
theorem isDualizable_ihom_obj {X : C} (hX : IsDualizable X) :
    IsDualizable ((ihom X).obj W) :=
  (hX.ihom_unit.tensorObj hT.isDualizable).of_iso (ihomIsoIhomUnitTensor γ hT X).symm

include γ hT in
/-- Biduality relative to an object `W` isomorphic to an invertible object: for a dualizable
`X` the double-dual map `X ⟶ [[X, W], W]` is an isomorphism. -/
theorem isIso_toIhomIhom_of_isDualizable {X : C} (hX : IsDualizable X) :
    IsIso (toIhomIhom W X) := by
  obtain ⟨_⟩ := hX
  have := isIso_toIhomIhomUnit X
  rw [← toIhomIhom_comp_ihomIhomIsoIhomIhomUnit_hom γ hT X] at this
  exact IsIso.of_isIso_comp_right _ (ihomIhomIsoIhomIhomUnit γ hT X).hom

/-- Duality into an object `W` isomorphic to an invertible object restricts to an
anti-equivalence of the dualizable objects, with quasi-inverse itself: the unit and the counit
are the double-dual isomorphisms `X ≅ [[X, W], W]`
(`CategoryTheory.MonoidalClosed.isIso_toIhomIhom_of_isDualizable`). -/
noncomputable def dualizableIhomEquivalence :
    (ObjectProperty.FullSubcategory (IsDualizable (C := C)))ᵒᵖ ≌
      ObjectProperty.FullSubcategory (IsDualizable (C := C)) :=
  ObjectProperty.liftDualEquivalence _ (internalHom.flip.obj W)
    (fun _ hX ↦ isDualizable_ihom_obj γ hT hX) (toIhomIhomNatTrans W)
    (fun _ hX ↦ isIso_toIhomIhom_of_isDualizable γ hT hX)

end Braided

end CategoryTheory.MonoidalClosed
