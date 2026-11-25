/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category

/-!

# Dualizable and invertible objects of a monoidal category

`CategoryTheory.HasRightDual` is a class carrying a right dual as *data*. This file records
the corresponding *property*, `CategoryTheory.IsDualizable X`, that some right dual exists,
together with the stronger property `CategoryTheory.IsInvertible X` that `X` admits a
two-sided tensor inverse (`CategoryTheory.IsInvertible.isDualizable`).

## Main definitions

- `CategoryTheory.IsDualizable`: `X` admits a right dual.
- `CategoryTheory.IsInvertible`: `X` admits a two-sided tensor inverse.
- `CategoryTheory.hasRightDualOfIso`: a right dual transported along an isomorphism.
- `CategoryTheory.hasRightDualOfIsZero`: a zero object is its own right dual.
- `CategoryTheory.exactPairingOfTensorIso`: the exact pairing of an object with a two-sided
  tensor inverse.
- `CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`: for an exact pairing of `Y` and `X`, the
  internal hom `ihom X` is `Y ⊗ -`.
- `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`: the canonical comparison map
  `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`.
- `CategoryTheory.tensorRightEquivalenceOfTensorIso`: tensoring on the right with an object
  with a two-sided tensor inverse is an equivalence.
- `CategoryTheory.MonoidalClosed.ihomTensorToIhom`: the canonical comparison map
  `(ihom X).obj Z ⊗ N ⟶ (ihom X).obj (Z ⊗ N)`.

## Main statements

- `CategoryTheory.isDualizable_of_tensorIso`, `CategoryTheory.IsInvertible.isDualizable`: an
  object with a two-sided tensor inverse is dualizable.
- `CategoryTheory.MonoidalClosed.curry_evaluation`: the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of
  the evaluation of an exact pairing of `Y` and `X` is an isomorphism.
- `CategoryTheory.MonoidalClosed.isIso_ihomUnitTensorToIhom`: the comparison map is an
  isomorphism when `X` has a left dual.
- `CategoryTheory.MonoidalClosed.exactPairingOfIsIso`: conversely, if the comparison map
  `(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, `(ihom X).obj (𝟙_ C)` is a
  left dual of `X`.
- `CategoryTheory.MonoidalClosed.isIso_ihomTensorToIhom`: the comparison map
  `(ihom X).obj Z ⊗ N ⟶ (ihom X).obj (Z ⊗ N)` is an isomorphism when `N` is invertible.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- An object `X` of a monoidal category is *dualizable* if it admits a right dual, that is,
an object `Xᘁ` together with an exact pairing `X ⊗ Xᘁ ⟶ 𝟙_ C`, `𝟙_ C ⟶ Xᘁ ⊗ X`.

Unlike `CategoryTheory.HasRightDual`, which carries the dual as data, this is a `Prop`. -/
def IsDualizable (X : C) : Prop :=
  Nonempty (HasRightDual X)

theorem isDualizable_of_hasRightDual (X : C) [HasRightDual X] : IsDualizable X :=
  ⟨inferInstance⟩

theorem isDualizable_unit : IsDualizable (𝟙_ C) :=
  isDualizable_of_hasRightDual _

theorem IsDualizable.tensorObj {X Y : C} (hX : IsDualizable X) (hY : IsDualizable Y) :
    IsDualizable (X ⊗ Y) := by
  obtain ⟨_⟩ := hX
  obtain ⟨_⟩ := hY
  exact ⟨hasRightDualTensor⟩

/-- Dualizability is invariant under isomorphism. -/
theorem IsDualizable.of_iso {X Y : C} (e : X ≅ Y) (hX : IsDualizable X) : IsDualizable Y := by
  obtain ⟨_⟩ := hX
  exact ⟨{ rightDual := Xᘁ, exact := exactPairingCongrLeft e.symm }⟩

/-- A right dual of an object transported along an isomorphism. -/
noncomputable abbrev hasRightDualOfIso {P Q : C} (e : P ≅ Q) [HasRightDual Q] : HasRightDual P :=
  @HasRightDual.mk _ _ _ _ Qᘁ (exactPairingCongrLeft e)

open Limits in
/-- A zero object is its own right dual. -/
@[instance_reducible]
noncomputable def hasRightDualOfIsZero [HasZeroMorphisms C] {Z : C} (hZ : IsZero Z) :
    HasRightDual Z where
  rightDual := Z
  exact :=
    { coevaluation' := 0
      evaluation' := 0
      coevaluation_evaluation' := (hZ.of_iso (ρ_ Z)).eq_of_src _ _
      evaluation_coevaluation' := (hZ.of_iso (λ_ Z)).eq_of_src _ _ }

/-- The counit of the adjunction `- ⊗ Y ⊣ - ⊗ Y'` of an exact pairing of `Y` and `Y'` is the
evaluation `(X ⊗ Y') ⊗ Y ≅ X ⊗ (Y' ⊗ Y) ⟶ X`. -/
theorem tensorRightAdjunction_counit_app (Y Y' : C) [ExactPairing Y Y'] (X : C) :
    (tensorRightAdjunction Y Y').counit.app X =
      (α_ X Y' Y).hom ≫ X ◁ ε_ Y Y' ≫ (ρ_ X).hom := by
  simp [tensorRightAdjunction, tensorRightHomEquiv]

/-- An object `X` of a monoidal category is *invertible* if it admits a two-sided tensor
inverse, that is, an object `Y` with `X ⊗ Y ≅ 𝟙_ C` and `Y ⊗ X ≅ 𝟙_ C`. The Tate twists of the
`ℓ`-adic formalism are the motivating example.

Both isomorphisms are required: without a braiding, `X ⊗ Y ≅ 𝟙_ C` alone does not make `X`
invertible (for endofunctors under composition it only says that `X` has a section). -/
def IsInvertible (X : C) : Prop :=
  ∃ Y, Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)

theorem isInvertible_unit : IsInvertible (𝟙_ C) :=
  ⟨𝟙_ C, ⟨λ_ _⟩, ⟨λ_ _⟩⟩

/-- In a braided monoidal category a one-sided tensor inverse is two-sided. -/
theorem isInvertible_iff_of_braided [BraidedCategory C] (X : C) :
    IsInvertible X ↔ ∃ Y, Nonempty (X ⊗ Y ≅ 𝟙_ C) :=
  ⟨fun ⟨Y, e, _⟩ ↦ ⟨Y, e⟩, fun ⟨Y, ⟨e⟩⟩ ↦ ⟨Y, ⟨e⟩, ⟨β_ Y X ≪≫ e⟩⟩⟩

/-- An object `X` with a two-sided tensor inverse `Y`, `X ⊗ Y ≅ 𝟙_ C ≅ Y ⊗ X`, forms an exact
pairing with `Y`. The coevaluation is the inverse of `X ⊗ Y ≅ 𝟙_ C`; the evaluation is
`Y ⊗ X ≅ 𝟙_ C` corrected by an automorphism of `X` so that the first zigzag identity holds,
and the second zigzag identity then follows, since `- ▷ X` is injective. -/
@[instance_reducible]
noncomputable def exactPairingOfTensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    ExactPairing X Y :=
  let φ : X ⟶ X := (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ e'.hom ≫ (ρ_ X).hom
  let ε : Y ⊗ X ⟶ 𝟙_ C := Y ◁ inv φ ≫ e'.hom
  have zig : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = 𝟙 X := by
    have : (λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom = inv φ ≫ φ := by
      simp only [ε, φ, MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
        leftUnitor_inv_naturality_assoc]
    rw [this, IsIso.inv_hom_id]
  have zag : (ρ_ Y).inv ≫ Y ◁ e.inv ≫ (α_ Y X Y).inv ≫ ε ▷ Y ≫ (λ_ Y).hom = 𝟙 Y := by
    apply whiskerRight_injective_of_tensorIso e
    rw [id_whiskerRight, ← cancel_mono ε, Category.id_comp]
    calc _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          ε ▷ (Y ⊗ X) ≫ (λ_ (Y ⊗ X)).hom ≫ ε := by monoidal
      _ = (ρ_ Y).inv ▷ X ≫ (Y ◁ e.inv) ▷ X ≫ (α_ Y X Y).inv ▷ X ≫ (α_ (Y ⊗ X) Y X).hom ≫
          (Y ⊗ X) ◁ ε ≫ (ρ_ (Y ⊗ X)).hom ≫ ε := by
        rw [whiskerRight_comp_leftUnitor_hom_comp]
      _ = Y ◁ ((λ_ X).inv ≫ e.inv ▷ X ≫ (α_ X Y X).hom ≫ X ◁ ε ≫ (ρ_ X).hom) ≫ ε := by
        monoidal
      _ = ε := by rw [zig, whiskerLeft_id, Category.id_comp]
  { coevaluation' := e.inv
    evaluation' := ε
    coevaluation_evaluation' := by
      rw [← cancel_epi (ρ_ Y).inv, ← cancel_mono (λ_ Y).hom]
      simpa using zag
    evaluation_coevaluation' := by
      rw [← cancel_epi (λ_ X).inv, ← cancel_mono (ρ_ X).hom]
      simpa using zig }

/-- An object with a two-sided tensor inverse is dualizable. -/
theorem isDualizable_of_tensorIso {X Y : C} (e : X ⊗ Y ≅ 𝟙_ C) (e' : Y ⊗ X ≅ 𝟙_ C) :
    IsDualizable X :=
  letI := exactPairingOfTensorIso e e'
  ⟨⟨Y⟩⟩

/-- An invertible object is dualizable. -/
theorem IsInvertible.isDualizable {X : C} (hX : IsInvertible X) : IsDualizable X := by
  obtain ⟨Y, ⟨e⟩, ⟨e'⟩⟩ := hX
  exact isDualizable_of_tensorIso e e'

section

universe v u

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Tensoring on the right with an object `N` with a two-sided tensor inverse `N'` is an
equivalence of categories, with quasi-inverse tensoring on the right with `N'`. -/
@[simps! functor_obj inverse_obj]
noncomputable def tensorRightEquivalenceOfTensorIso {N N' : D} (e : N ⊗ N' ≅ 𝟙_ D)
    (e' : N' ⊗ N ≅ 𝟙_ D) : D ≌ D :=
  Equivalence.mk (tensorRight N) (tensorRight N')
    (NatIso.ofComponents (fun Z ↦ (ρ_ Z).symm ≪≫ whiskerLeftIso Z e.symm ≪≫ (α_ Z N N').symm)
      (fun f ↦ by
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Functor.id_map,
          Functor.comp_map, Category.assoc]
        erw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
          associator_inv_naturality_left]
        rfl))
    (NatIso.ofComponents (fun Z ↦ α_ Z N' N ≪≫ whiskerLeftIso Z e' ≪≫ ρ_ Z)
      (fun f ↦ by
        simp only [Iso.trans_hom, whiskerLeftIso_hom, Functor.id_map,
          Functor.comp_map, Category.assoc]
        change (f ▷ N') ▷ N ≫ _ = _
        erw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
          rightUnitor_naturality]))

end

/-- The counit of `tensorLeftAdjunction Y X : tensorLeft X ⊣ tensorLeft Y` at `Z` is the composite
```
              α⁻¹                 ε_ Y X ▷ Z            λ_ Z
  X ⊗ (Y ⊗ Z) ───→ (X ⊗ Y) ⊗ Z ──────────→ 𝟙_ C ⊗ Z ─────→ Z.
```
-/
theorem tensorLeftAdjunction_counit_app (Y X : C) [ExactPairing Y X] (Z : C) :
    (tensorLeftAdjunction Y X).counit.app Z = (α_ _ _ _).inv ≫ ε_ Y X ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

namespace MonoidalClosed

variable [MonoidalClosed C]

/-- If `Y` is a left dual of `X`, that is, `Y` and `X` form an exact pairing, then the internal
hom `ihom X` of a monoidal closed category is tensoring on the left with `Y`: both are right
adjoint to `X ⊗ -`. -/
noncomputable def ihomIsoTensorLeft (Y X : C) [ExactPairing Y X] : ihom X ≅ tensorLeft Y :=
  (ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)

/-- If `Y` is a left dual of `X`, then `(ihom X).obj Z ≅ Y ⊗ Z`. -/
noncomputable def ihomObjIsoTensor (Y X : C) [ExactPairing Y X] (Z : C) :
    (ihom X).obj Z ≅ Y ⊗ Z :=
  (ihomIsoTensorLeft Y X).app Z

/-- If `Y` is a left dual of `X`, then the internal dual `(ihom X).obj (𝟙_ C)` is `Y`. -/
noncomputable def ihomObjUnitIso (Y X : C) [ExactPairing Y X] : (ihom X).obj (𝟙_ C) ≅ Y :=
  ihomObjIsoTensor Y X (𝟙_ C) ≪≫ ρ_ Y

/-- The canonical comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z`: the transpose of
`X ⊗ ((ihom X).obj (𝟙_ C) ⊗ Z) ≅ (X ⊗ (ihom X).obj (𝟙_ C)) ⊗ Z ⟶ 𝟙_ C ⊗ Z ≅ Z`, built from
the evaluation `X ⊗ (ihom X).obj (𝟙_ C) ⟶ 𝟙_ C`. -/
noncomputable def ihomUnitTensorToIhom (X Z : C) : (ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z :=
  curry ((α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom)

/-- If `Y` is a left dual of `X`, the comparison map is identified with `ihomObjIsoTensor`:
the square
```
                              ihomUnitTensorToIhom X Z
  (ihom X).obj (𝟙_ C) ⊗ Z ──────────────────────────→ (ihom X).obj Z
              │                                              │
  (ihomObjUnitIso Y X).hom ▷ Z               (ihomObjIsoTensor Y X Z).hom
              ↓                                              ↓
            Y ⊗ Z ═══════════════════════════════════════ Y ⊗ Z
```
commutes. -/
theorem ihomUnitTensorToIhom_eq (Y X : C) [ExactPairing Y X] (Z : C) :
    ihomUnitTensorToIhom X Z = (ihomObjUnitIso Y X).hom ▷ Z ≫ (ihomObjIsoTensor Y X Z).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  have h₂ := (tensorLeftAdjunction Y X).rightAdjointUniq_hom_app_counit (ihom.adjunction X) Z
  rw [tensorLeftAdjunction_counit_app] at h₁ h₂
  dsimp only [ihom.ihom_adjunction_counit] at h₁ h₂
  simp only [curriedTensor_obj_map] at h₁ h₂
  simp only [ihomUnitTensorToIhom, curry_eq_iff, uncurry_eq, ihomObjUnitIso, ihomObjIsoTensor,
    ihomIsoTensorLeft, Iso.trans_hom, Iso.app_inv, Adjunction.rightAdjointUniq_inv_app,
    Iso.app_hom]
  rw [← h₁, MonoidalCategory.whiskerLeft_comp_assoc, h₂]
  monoidal

/-- If `Y` is a left dual of `X`, the transpose `Y ⟶ (ihom X).obj (𝟙_ C)` of the evaluation
`ε_ Y X : X ⊗ Y ⟶ 𝟙_ C` is the inverse of `ihomObjUnitIso Y X`. -/
theorem curry_evaluation (Y X : C) [ExactPairing Y X] :
    curry (ε_ Y X) = (ihomObjUnitIso Y X).inv := by
  have h₁ := (ihom.adjunction X).rightAdjointUniq_hom_app_counit (tensorLeftAdjunction Y X) (𝟙_ C)
  rw [tensorLeftAdjunction_counit_app] at h₁
  dsimp only [ihom.ihom_adjunction_counit] at h₁
  rw [curry_eq_iff, uncurry_eq, ← h₁]
  simp only [ihomObjUnitIso, ihomObjIsoTensor, ihomIsoTensorLeft, Iso.trans_inv, Iso.app_inv,
    curriedTensor_obj_map, MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc X
    (((ihom.adjunction X).rightAdjointUniq (tensorLeftAdjunction Y X)).inv.app (𝟙_ C)),
    Iso.inv_hom_id_app]
  monoidal

instance isIso_curry_evaluation (Y X : C) [ExactPairing Y X] :
    IsIso (curry (ε_ Y X)) := by
  rw [curry_evaluation]
  infer_instance

/-- If `X` has a left dual, the comparison map `(ihom X).obj (𝟙_ C) ⊗ Z ⟶ (ihom X).obj Z` is an
isomorphism. -/
theorem isIso_ihomUnitTensorToIhom (Y X : C) [ExactPairing Y X] (Z : C) :
    IsIso (ihomUnitTensorToIhom X Z) := by
  rw [ihomUnitTensorToIhom_eq Y X]
  infer_instance

/-- The transpose of `ihomUnitTensorToIhom X Z` is evaluation of the first factor:
```
X ⊗ ([X, 𝟙] ⊗ Z) --X ◁ ihomUnitTensorToIhom--> X ⊗ [X, Z]
        |                                          |
       α⁻¹                                        ev
        v                                          v
(X ⊗ [X, 𝟙]) ⊗ Z ------ev ▷ Z------> 𝟙 ⊗ Z ---λ---> Z
```
-/
lemma whiskerLeft_ihomUnitTensorToIhom_ev (X Z : C) :
    X ◁ ihomUnitTensorToIhom X Z ≫ (ihom.ev X).app Z =
      (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ Z ≫ (λ_ Z).hom := by
  rw [← uncurry_eq, ihomUnitTensorToIhom, uncurry_curry]

/-- The canonical comparison map `(ihom X).obj Z ⊗ N ⟶ (ihom X).obj (Z ⊗ N)`: the transpose of
`X ⊗ ((ihom X).obj Z ⊗ N) ≅ (X ⊗ (ihom X).obj Z) ⊗ N ⟶ Z ⊗ N`, built from the evaluation
`X ⊗ (ihom X).obj Z ⟶ Z`. -/
noncomputable def ihomTensorToIhom (X Z N : C) : (ihom X).obj Z ⊗ N ⟶ (ihom X).obj (Z ⊗ N) :=
  curry ((α_ _ _ _).inv ≫ (ihom.ev X).app Z ▷ N)

/-- The transpose of `ihomTensorToIhom X Z N` is evaluation of the first factor. -/
lemma whiskerLeft_ihomTensorToIhom_ev (X Z N : C) :
    X ◁ ihomTensorToIhom X Z N ≫ (ihom.ev X).app (Z ⊗ N) =
      (α_ _ _ _).inv ≫ (ihom.ev X).app Z ▷ N := by
  rw [← uncurry_eq, ihomTensorToIhom, uncurry_curry]

/-- Precomposing `ihomTensorToIhom X Z N` with `f ▷ N` transposes to `uncurry f ▷ N`. -/
lemma uncurry_whiskerRight_comp_ihomTensorToIhom {X Z N T : C} (f : T ⟶ (ihom X).obj Z) :
    uncurry (f ▷ N ≫ ihomTensorToIhom X Z N) = (α_ _ _ _).inv ≫ uncurry f ▷ N := by
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_ihomTensorToIhom_ev, associator_inv_naturality_middle_assoc, comp_whiskerRight]

/-- The canonical map `[X, Z] ⊗ N ⟶ [X, Z ⊗ N]` is natural in `X`: for `f : X ⟶ Y` the square
```
  [Y, Z] ⊗ N ── ihomTensorToIhom ──→ [Y, Z ⊗ N]
       │                                  │
  [f, Z] ▷ N                         [f, Z ⊗ N]
       ↓                                  ↓
  [X, Z] ⊗ N ── ihomTensorToIhom ──→ [X, Z ⊗ N]
```
commutes. -/
@[reassoc]
lemma pre_app_whiskerRight_comp_ihomTensorToIhom {X Y : C} (f : X ⟶ Y) (Z N : C) :
    (pre f).app Z ▷ N ≫ ihomTensorToIhom X Z N =
      ihomTensorToIhom Y Z N ≫ (pre f).app (Z ⊗ N) := by
  apply uncurry_injective
  rw [uncurry_whiskerRight_comp_ihomTensorToIhom, uncurry_pre_app, uncurry_pre,
    ihomTensorToIhom, uncurry_curry, associator_inv_naturality_left_assoc, comp_whiskerRight]

/-- The canonical map `[X, Z] ⊗ N ⟶ [X, Z ⊗ N]` is compatible with internal currying: the
square
```
  [K ⊗ A, Z] ⊗ N ─────────── ihomTensorToIhom ───────────→ [K ⊗ A, Z ⊗ N]
        │                                                          │
  ihomCurry ▷ N                                                ihomCurry
        ↓                                                          ↓
  [A, [K, Z]] ⊗ N ─ ihomTensorToIhom ─→ [A, [K, Z] ⊗ N] ─ [A, ihomTensorToIhom] ─→ [A, [K, Z ⊗ N]]
```
commutes. -/
@[reassoc]
lemma ihomTensorToIhom_comp_ihomCurry (K A Z N : C) :
    ihomTensorToIhom (K ⊗ A) Z N ≫ ihomCurry K A (Z ⊗ N) =
      ihomCurry K A Z ▷ N ≫ ihomTensorToIhom A ((ihom K).obj Z) N ≫
        (ihom A).map (ihomTensorToIhom K Z N) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc, ihomTensorToIhom,
    ihomCurry, ihom.ev_naturality, whiskerLeft_curry_ihom_ev_app]
  rw [associator_inv_naturality_right_assoc, whiskerLeft_curry_ihom_ev_app,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Category.assoc, whiskerLeft_curry_ihom_ev_app,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight,
    whiskerLeft_curry_ihom_ev_app, MonoidalCategory.whiskerLeft_comp_assoc]
  have key {Y : C} (c : Y ⟶ (ihom K).obj Z) :
      K ◁ c ▷ N ≫ (α_ _ _ _).inv ≫ (ihom.ev K).app Z ▷ N =
        (α_ _ _ _).inv ≫ (K ◁ c ≫ (ihom.ev K).app Z) ▷ N := by
    rw [associator_inv_naturality_middle_assoc, comp_whiskerRight]
  rw [key, whiskerLeft_curry_ihom_ev_app]
  monoidal

/-- Blueprint `theorem-poincare-duality--2`: Internal Hom with an invertible twist (the
categorical core).

In a monoidal closed category, for every invertible object `N` the canonical map
`(ihom X).obj Z ⊗ N ⟶ (ihom X).obj (Z ⊗ N)` is an isomorphism, for all `X` and `Z`. Since
`- ⊗ N` is an autoequivalence, both sides corepresent the same functor
`T ↦ (X ⊗ T ⊗ N⁻¹ ⟶ Z)`, and the canonical map induces this identification (Yoneda). No
hypothesis on `X` is needed. -/
theorem isIso_ihomTensorToIhom (X Z : C) {N : C} (hN : IsInvertible N) :
    IsIso (ihomTensorToIhom X Z N) := by
  obtain ⟨N', ⟨e⟩, ⟨e'⟩⟩ := hN
  let E := tensorRightEquivalenceOfTensorIso e e'
  have inj {T : C} (a a' : T ⟶ (ihom X).obj Z)
      (h : a ▷ N ≫ ihomTensorToIhom X Z N = a' ▷ N ≫ ihomTensorToIhom X Z N) : a = a' := by
    apply uncurry_injective
    apply whiskerRight_injective_of_tensorIso e
    rw [← cancel_epi (α_ _ _ _).inv, ← uncurry_whiskerRight_comp_ihomTensorToIhom,
      ← uncurry_whiskerRight_comp_ihomTensorToIhom, h]
  have surj {T : C} (g : T ⊗ N ⟶ (ihom X).obj (Z ⊗ N)) :
      ∃ a : T ⟶ (ihom X).obj Z, a ▷ N ≫ ihomTensorToIhom X Z N = g := by
    let b : X ⊗ T ⟶ Z := E.functor.preimage ((α_ _ _ _).hom ≫ uncurry g)
    have hb : b ▷ N = (α_ _ _ _).hom ≫ uncurry g := E.functor.map_preimage _
    refine ⟨curry b, uncurry_injective ?_⟩
    rw [uncurry_whiskerRight_comp_ihomTensorToIhom, uncurry_curry, hb, Iso.inv_hom_id_assoc]
  refine isIso_of_yoneda_map_bijective _ (fun T ↦ ⟨fun x x' h ↦ ?_, fun g ↦ ?_⟩)
  · let ι := E.counitIso.app T
    let a : E.inverse.obj T ⟶ (ihom X).obj Z := E.functor.preimage (ι.hom ≫ x)
    let a' : E.inverse.obj T ⟶ (ihom X).obj Z := E.functor.preimage (ι.hom ≫ x')
    have ha : a ▷ N = ι.hom ≫ x := E.functor.map_preimage _
    have ha' : a' ▷ N = ι.hom ≫ x' := E.functor.map_preimage _
    have h : x ≫ ihomTensorToIhom X Z N = x' ≫ ihomTensorToIhom X Z N := h
    rw [← cancel_epi ι.hom, ← ha, ← ha', inj a a' (by rw [ha, ha', Category.assoc,
      Category.assoc, h])]
  · obtain ⟨a, ha⟩ := surj ((E.counitIso.app T).hom ≫ g)
    refine ⟨(E.counitIso.app T).inv ≫ a ▷ N, ?_⟩
    dsimp only
    rw [Category.assoc, ha, Iso.inv_hom_id_assoc]

variable (X : C) [IsIso (ihomUnitTensorToIhom X X)]

/-- If the comparison map `(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, the
coevaluation `𝟙_ C ⟶ (ihom X).obj (𝟙_ C) ⊗ X` is the preimage of the transpose of `ρ_ X`. -/
noncomputable def coevaluationOfIsIso : 𝟙_ C ⟶ (ihom X).obj (𝟙_ C) ⊗ X :=
  curry (ρ_ X).hom ≫ inv (ihomUnitTensorToIhom X X)

/-- The first zigzag identity for `coevaluationOfIsIso`. -/
lemma coevaluationOfIsIso_evaluation :
    X ◁ coevaluationOfIsIso X ≫ (α_ _ _ _).inv ≫ (ihom.ev X).app (𝟙_ C) ▷ X =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [← cancel_mono (λ_ X).hom, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← whiskerLeft_ihomUnitTensorToIhom_ev, coevaluationOfIsIso,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, ← uncurry_eq, uncurry_curry]

/-- The second zigzag identity for `coevaluationOfIsIso`. -/
lemma evaluation_coevaluationOfIsIso :
    coevaluationOfIsIso X ▷ (ihom X).obj (𝟙_ C) ≫ (α_ _ _ _).hom ≫
      (ihom X).obj (𝟙_ C) ◁ (ihom.ev X).app (𝟙_ C) =
      (λ_ _).hom ≫ (ρ_ _).inv := by
  apply (cancel_mono (ρ_ _).hom).1
  apply cancel_epi (λ_ _).inv |>.1
  apply uncurry_injective
  simp only [uncurry_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    MonoidalCategory.whiskerLeft_comp]
  set D := (ihom X).obj (𝟙_ C)
  set e : X ⊗ D ⟶ 𝟙_ C := (ihom.ev X).app (𝟙_ C)
  have key : X ◁ D ◁ e ≫ X ◁ (ρ_ D).hom ≫ e =
      (α_ X D (X ⊗ D)).inv ≫ e ▷ (X ⊗ D) ≫ (λ_ _).hom ≫ e := by
    rw [MonoidalCategory.whiskerLeft_rightUnitor, Category.assoc,
      associator_inv_naturality_right_assoc, ← rightUnitor_naturality, whisker_exchange_assoc,
      ← unitors_equal, leftUnitor_naturality]
  rw [key, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have z := coevaluationOfIsIso_evaluation X
  calc _ = X ◁ (λ_ D).inv ≫ (α_ X (𝟙_ C) D).inv ≫
        (X ◁ coevaluationOfIsIso X ≫ (α_ _ _ _).inv ≫ e ▷ X) ▷ D ≫ (α_ (𝟙_ C) X D).hom ≫
          (λ_ _).hom ≫ e := by monoidal
    _ = e := by rw [z]; monoidal

/-- **A criterion for left duals**: if the comparison map
`(ihom X).obj (𝟙_ C) ⊗ X ⟶ (ihom X).obj X` is an isomorphism, then `(ihom X).obj (𝟙_ C)` is a
left dual of `X`, with evaluation the evaluation of the internal hom. -/
@[instance_reducible]
noncomputable def exactPairingOfIsIso : ExactPairing ((ihom X).obj (𝟙_ C)) X where
  coevaluation' := coevaluationOfIsIso X
  evaluation' := (ihom.ev X).app (𝟙_ C)
  coevaluation_evaluation' := coevaluationOfIsIso_evaluation X
  evaluation_coevaluation' := evaluation_coevaluationOfIsIso X

end MonoidalClosed

end CategoryTheory
