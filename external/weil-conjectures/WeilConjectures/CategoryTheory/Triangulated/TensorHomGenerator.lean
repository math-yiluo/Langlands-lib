/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.RingTheory.Flat.Basic

/-!
# Base change of morphisms along triangulated functors

Let `F → F'` be a flat algebra (for instance a field extension), `C` an `F`-linear and `D` an
`F'`-linear pretriangulated category, and `Φ : C ⥤ D` a triangulated functor sending `c • f` to
`c • Φ f`. For objects `X`, `Y` of `C`, `Φ` induces a morphism of groups
`F' ⊗_F Hom(X, Y) ⟶ Hom(Φ X, Φ Y)`, `a ⊗ f ↦ a • Φ f` (`CategoryTheory.Functor.tensorHom`). As
for `CategoryTheory.Functor.HomBijective`, the five lemma (`Mathlib.Algebra.FiveLemma`) applied to
the long exact `Hom` sequences of distinguished triangles, tensored with the flat `F`-module `F'`,
shows that the objects for which these maps are bijective form triangulated subcategories, so
that bijectivity on a generator implies bijectivity on everything it generates
(`CategoryTheory.Functor.tensorBijective_of_generator`).
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive ZeroObject TensorProduct

namespace Functor

variable {F F' : Type*} [CommRing F] [CommRing F'] [Algebra F F']
  {C D : Type*} [Category* C] [Category* D] [Preadditive C] [CategoryTheory.Linear F C]
  [Preadditive D] [CategoryTheory.Linear F' D] (Φ : C ⥤ D) [Φ.Additive]
  (hΦ : ∀ (c : F) {X Y : C} (f : X ⟶ Y), Φ.map (c • f) = algebraMap F F' c • Φ.map f)

/-- The morphism `F' ⊗_F Hom(X, Y) ⟶ Hom(Φ X, Φ Y)`, `a ⊗ f ↦ a • Φ f`. -/
noncomputable def tensorHom (X Y : C) : F' ⊗[F] (X ⟶ Y) →+ (Φ.obj X ⟶ Φ.obj Y) :=
  letI : Module F (Φ.obj X ⟶ Φ.obj Y) := Module.compHom _ (algebraMap F F')
  (TensorProduct.lift (LinearMap.mk₂ F (fun (a : F') (f : X ⟶ Y) ↦ a • Φ.map f)
    (fun a b f ↦ add_smul a b _)
    (fun c a f ↦ by
      change (c • a) • Φ.map f = algebraMap F F' c • a • Φ.map f
      rw [Algebra.smul_def, mul_smul])
    (fun a f g ↦ by simp)
    (fun c a f ↦ by
      change a • Φ.map (c • f) = algebraMap F F' c • a • Φ.map f
      rw [hΦ, smul_comm]))).toAddMonoidHom

@[simp]
lemma tensorHom_tmul {X Y : C} (a : F') (f : X ⟶ Y) :
    Φ.tensorHom hΦ X Y (a ⊗ₜ f) = a • Φ.map f := by
  simp [tensorHom]

lemma tensorHom_lTensor_rightComp {X Y Z : C} (g : Y ⟶ Z) (t : F' ⊗[F] (X ⟶ Y)) :
    Φ.tensorHom hΦ X Z ((Linear.rightComp F X g).lTensor F' t) =
      Φ.tensorHom hΦ X Y t ≫ Φ.map g := by
  induction t using TensorProduct.inductionOn with
  | tmul a f => simp
  | add x y hx hy => simp [hx, hy]

lemma tensorHom_lTensor_leftComp {X Y Z : C} (f : X ⟶ Y) (t : F' ⊗[F] (Y ⟶ Z)) :
    Φ.tensorHom hΦ X Z ((Linear.leftComp F Z f).lTensor F' t) =
      Φ.map f ≫ Φ.tensorHom hΦ Y Z t := by
  induction t using TensorProduct.inductionOn with
  | tmul a g => simp
  | add x y hx hy => simp [hx, hy]

attribute [irreducible] tensorHom

/-- The map `F' ⊗_F Hom(X, Y) ⟶ Hom(Φ X, Φ Y)` is bijective. -/
def TensorBijective (X Y : C) : Prop := Function.Bijective (Φ.tensorHom hΦ X Y)

variable {Φ hΦ}

lemma TensorBijective.of_iso {X Y X' Y' : C} (h : Φ.TensorBijective hΦ X Y) (e : X ≅ X')
    (e' : Y ≅ Y') : Φ.TensorBijective hΦ X' Y' := by
  let u : (X ⟶ Y) ≃ₗ[F] (X' ⟶ Y') :=
    { toFun := fun f ↦ e.inv ≫ f ≫ e'.hom
      invFun := fun f ↦ e.hom ≫ f ≫ e'.inv
      map_add' := by simp
      map_smul' := by simp
      left_inv := fun f ↦ by simp
      right_inv := fun f ↦ by simp }
  have : (Φ.tensorHom hΦ X' Y' : _ → _) =
      (fun g ↦ Φ.map e.inv ≫ g ≫ Φ.map e'.hom) ∘ Φ.tensorHom hΦ X Y ∘
        (u.symm.lTensor F') := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul a f =>
      simp only [Function.comp_apply, LinearEquiv.lTensor_tmul, tensorHom_tmul, u]
      simp [← Functor.map_comp]
    | add x y hx hy =>
      simp only [Function.comp_apply] at hx hy ⊢
      rw [_root_.map_add, hx, hy, _root_.map_add, _root_.map_add, add_comp, comp_add]
  unfold TensorBijective
  rw [this]
  exact (Iso.homCongr (Φ.mapIso e) (Φ.mapIso e')).bijective.comp
    (h.comp (u.symm.lTensor F').bijective)

lemma TensorBijective.of_isZero_left {X Y : C} (hX : IsZero X) :
    Φ.TensorBijective hΦ X Y := by
  have : Subsingleton (X ⟶ Y) := ⟨fun _ _ ↦ hX.eq_of_src _ _⟩
  have : Subsingleton (F' ⊗[F] (X ⟶ Y)) := by
    refine ⟨fun s t ↦ ?_⟩
    have h (s : F' ⊗[F] (X ⟶ Y)) : s = 0 := by
      induction s using TensorProduct.inductionOn with
      | tmul a f => rw [Subsingleton.elim f 0, tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h s, h t]
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, (Φ.map_isZero hX).eq_of_src _ _⟩⟩

lemma TensorBijective.of_isZero_right {X Y : C} (hY : IsZero Y) :
    Φ.TensorBijective hΦ X Y := by
  have : Subsingleton (X ⟶ Y) := ⟨fun _ _ ↦ hY.eq_of_tgt _ _⟩
  have : Subsingleton (F' ⊗[F] (X ⟶ Y)) := by
    refine ⟨fun s t ↦ ?_⟩
    have h (s : F' ⊗[F] (X ⟶ Y)) : s = 0 := by
      induction s using TensorProduct.inductionOn with
      | tmul a f => rw [Subsingleton.elim f 0, tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h s, h t]
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, (Φ.map_isZero hY).eq_of_tgt _ _⟩⟩

section Exact

variable {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
  [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]

omit [Φ.Additive] in
lemma exact_rightComp_of_distTriang (T : Triangle E) (hT : T ∈ distTriang E) (X : E) :
    Function.Exact (rightComp X T.mor₁) (rightComp X T.mor₂) := fun y ↦
  ⟨fun hy ↦ by
    obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₂ T hT y hy
    exact ⟨g, rfl⟩,
  by
    rintro ⟨g, rfl⟩
    change (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [assoc, comp_distTriang_mor_zero₁₂ _ hT, comp_zero]⟩

omit [Φ.Additive] in
lemma exact_leftComp_of_distTriang (T : Triangle E) (hT : T ∈ distTriang E) (Y : E) :
    Function.Exact (leftComp Y T.mor₂) (leftComp Y T.mor₁) := fun y ↦
  ⟨fun hy ↦ by
    obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₂ T hT y hy
    exact ⟨g, rfl⟩,
  by
    rintro ⟨g, rfl⟩
    change T.mor₁ ≫ T.mor₂ ≫ g = 0
    rw [← assoc, comp_distTriang_mor_zero₁₂ _ hT, zero_comp]⟩

end Exact

lemma TensorBijective.of_subsingleton {X Y : C} [Subsingleton (X ⟶ Y)]
    [Subsingleton (Φ.obj X ⟶ Φ.obj Y)] : Φ.TensorBijective hΦ X Y := by
  have : Subsingleton (F' ⊗[F] (X ⟶ Y)) := by
    refine ⟨fun s t ↦ ?_⟩
    have h (s : F' ⊗[F] (X ⟶ Y)) : s = 0 := by
      induction s using TensorProduct.inductionOn with
      | tmul a f => rw [Subsingleton.elim f 0, tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h s, h t]
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [Φ.CommShift ℤ] [Φ.IsTriangulated] [Module.Flat F F']

/-- The five lemma for the covariant `Hom` sequences, tensored with `F'`. -/
lemma tensorBijective_obj₂_of_triangle (X : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₀ : Function.Surjective (Φ.tensorHom hΦ X T.invRotate.obj₁))
    (h₁ : Φ.TensorBijective hΦ X T.obj₁) (h₃ : Φ.TensorBijective hΦ X T.obj₃)
    (h₄ : Function.Injective (Φ.tensorHom hΦ X (T.obj₁⟦(1 : ℤ)⟧))) :
    Φ.TensorBijective hΦ X T.obj₂ := by
  have hT' := inv_rot_of_distTriang _ hT
  have hFT := Φ.map_distinguished _ hT
  have hFT' := Φ.map_distinguished _ hT'
  have e₁ (a b c : C) (u : a ⟶ b) (v : b ⟶ c) (h : Function.Exact (rightComp X u) (rightComp X v)) :
      Function.Exact ((Linear.rightComp F X u).lTensor F').toAddMonoidHom
        ((Linear.rightComp F X v).lTensor F').toAddMonoidHom :=
    Module.Flat.lTensor_exact F' (f := Linear.rightComp F X u) (g := Linear.rightComp F X v) h
  have c (a b : C) (u : a ⟶ b) :
      (rightComp _ (Φ.map u)).comp (Φ.tensorHom hΦ X a) =
        (Φ.tensorHom hΦ X b).comp ((Linear.rightComp F X u).lTensor F').toAddMonoidHom := by
    ext t
    exact (tensorHom_lTensor_rightComp Φ hΦ u t).symm
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((Linear.rightComp F X (T.invRotate.mor₁ : _ ⟶ T.obj₁)).lTensor F').toAddMonoidHom
    ((Linear.rightComp F X T.mor₁).lTensor F').toAddMonoidHom
    ((Linear.rightComp F X T.mor₂).lTensor F').toAddMonoidHom
    ((Linear.rightComp F X T.mor₃).lTensor F').toAddMonoidHom
    (rightComp _ (Φ.map (T.invRotate.mor₁ : _ ⟶ T.obj₁))) (rightComp _ (Φ.map T.mor₁))
    (rightComp _ (Φ.map T.mor₂)) (rightComp _ (Φ.map T.mor₃))
    (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _)
    (Φ.tensorHom hΦ _ _) (c _ _ _) (c _ _ _) (c _ _ _) (c _ _ _)
    (e₁ _ _ _ _ _ (exact_rightComp_of_distTriang _ hT' X))
    (e₁ _ _ _ _ _ (exact_rightComp_of_distTriang _ hT X))
    (e₁ _ _ _ _ _ (exact_rightComp_of_distTriang _ (rot_of_distTriang _ hT) X))
    (exact_rightComp_of_distTriang _ hFT' _) (exact_rightComp_of_distTriang _ hFT _)
    (fun y ↦ ⟨fun hy ↦ by
      obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ _ hFT y (by
        change y ≫ Φ.map T.mor₃ ≫ _ = 0
        rw [← assoc, show y ≫ Φ.map T.mor₃ = 0 from hy, zero_comp])
      exact ⟨g, rfl⟩, by
      rintro ⟨g, rfl⟩
      change (g ≫ Φ.map T.mor₂) ≫ Φ.map T.mor₃ = 0
      rw [assoc, ← Φ.map_comp, comp_distTriang_mor_zero₂₃ _ hT, Φ.map_zero, comp_zero]⟩)
    h₀ h₁ h₃ h₄

/-- The five lemma for the contravariant `Hom` sequences, tensored with `F'`. -/
lemma tensorBijective_obj₂_of_triangle' (Y : C) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₀ : Function.Surjective (Φ.tensorHom hΦ (T.obj₁⟦(1 : ℤ)⟧) Y))
    (h₁ : Φ.TensorBijective hΦ T.obj₃ Y) (h₃ : Φ.TensorBijective hΦ T.obj₁ Y)
    (h₄ : Function.Injective (Φ.tensorHom hΦ T.invRotate.obj₁ Y)) :
    Φ.TensorBijective hΦ T.obj₂ Y := by
  have hT' := inv_rot_of_distTriang _ hT
  have hFT := Φ.map_distinguished _ hT
  have hFT' := Φ.map_distinguished _ hT'
  have e₁ (a b c : C) (u : a ⟶ b) (v : b ⟶ c) (h : Function.Exact (leftComp Y v) (leftComp Y u)) :
      Function.Exact ((Linear.leftComp F Y v).lTensor F').toAddMonoidHom
        ((Linear.leftComp F Y u).lTensor F').toAddMonoidHom :=
    Module.Flat.lTensor_exact F' (f := Linear.leftComp F Y v) (g := Linear.leftComp F Y u) h
  have c (a b : C) (u : a ⟶ b) :
      (leftComp _ (Φ.map u)).comp (Φ.tensorHom hΦ b Y) =
        (Φ.tensorHom hΦ a Y).comp ((Linear.leftComp F Y u).lTensor F').toAddMonoidHom := by
    ext t
    exact (tensorHom_lTensor_leftComp Φ hΦ u t).symm
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((Linear.leftComp F Y T.mor₃).lTensor F').toAddMonoidHom
    ((Linear.leftComp F Y T.mor₂).lTensor F').toAddMonoidHom
    ((Linear.leftComp F Y T.mor₁).lTensor F').toAddMonoidHom
    ((Linear.leftComp F Y (T.invRotate.mor₁ : _ ⟶ T.obj₁)).lTensor F').toAddMonoidHom
    (leftComp _ (Φ.map T.mor₃)) (leftComp _ (Φ.map T.mor₂)) (leftComp _ (Φ.map T.mor₁))
    (leftComp _ (Φ.map (T.invRotate.mor₁ : _ ⟶ T.obj₁)))
    (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _) (Φ.tensorHom hΦ _ _)
    (Φ.tensorHom hΦ _ _) (c _ _ _) (c _ _ _) (c _ _ _) (c _ _ _)
    (e₁ _ _ _ _ _ (exact_leftComp_of_distTriang _ (rot_of_distTriang _ hT) Y))
    (e₁ _ _ _ _ _ (exact_leftComp_of_distTriang _ hT Y))
    (e₁ _ _ _ _ _ (exact_leftComp_of_distTriang _ hT' Y))
    (fun y ↦ ⟨fun hy ↦ by
      obtain ⟨g, rfl⟩ := Triangle.yoneda_exact₃ _ hFT y hy
      exact ⟨(Φ.commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫ g, by
        change Φ.map T.mor₃ ≫ _ ≫ g = (Φ.map T.mor₃ ≫ _) ≫ g
        rw [assoc]⟩, by
      rintro ⟨g, rfl⟩
      change Φ.map T.mor₂ ≫ Φ.map T.mor₃ ≫ g = 0
      rw [← assoc, ← Φ.map_comp, comp_distTriang_mor_zero₂₃ _ hT, Φ.map_zero, zero_comp]⟩)
    (exact_leftComp_of_distTriang _ hFT _) (exact_leftComp_of_distTriang _ hFT' _)
    h₀ h₁ h₃ h₄

section Shift

variable [∀ n : ℤ, (shiftFunctor C n).Linear F] [∀ n : ℤ, (shiftFunctor D n).Linear F']

omit [HasZeroObject C] [Pretriangulated C] [HasZeroObject D] [Pretriangulated D]
  [Φ.IsTriangulated] [Module.Flat F F'] in
lemma TensorBijective.shift {X Y : C} (h : Φ.TensorBijective hΦ X Y) (n : ℤ) :
    Φ.TensorBijective hΦ (X⟦n⟧) (Y⟦n⟧) := by
  let s : (X ⟶ Y) ≃ₗ[F] (X⟦n⟧ ⟶ Y⟦n⟧) :=
    { toFun := fun f ↦ f⟦n⟧'
      invFun := fun g ↦ (shiftFunctor C n).preimage g
      map_add' := by simp
      map_smul' := by simp [Functor.map_smul]
      left_inv := fun f ↦ by simp
      right_inv := fun g ↦ by simp }
  have : (Φ.tensorHom hΦ (X⟦n⟧) (Y⟦n⟧) : _ → _) ∘ (s.lTensor F') =
      (fun g ↦ (Φ.commShiftIso n).hom.app X ≫ g⟦n⟧' ≫ (Φ.commShiftIso n).inv.app Y) ∘
        Φ.tensorHom hΦ X Y := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul a f =>
      simp only [Function.comp_apply, LinearEquiv.lTensor_tmul, tensorHom_tmul, s,
        LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Functor.map_smul,
        Linear.smul_comp, Linear.comp_smul]
      congr 1
      simp
    | add x y hx hy =>
      simp only [Function.comp_apply] at hx hy ⊢
      rw [_root_.map_add, _root_.map_add, hx, hy, _root_.map_add, Functor.map_add, add_comp,
        comp_add]
  have hb : Function.Bijective
      ((Φ.tensorHom hΦ (X⟦n⟧) (Y⟦n⟧) : _ → _) ∘ (s.lTensor F')) := by
    rw [this]
    exact ((Iso.homCongr ((Φ.commShiftIso n).app X).symm
      ((Φ.commShiftIso n).app Y).symm).bijective.comp
        ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D n)).map_bijective _ _)).comp h
  exact (Function.Bijective.of_comp_iff _ (s.lTensor F').bijective).1 hb

variable (Φ hΦ) in
/-- `Φ` induces bijections `F' ⊗ Hom(X⟦a⟧, Y⟦b⟧) ≃ Hom(Φ (X⟦a⟧), Φ (Y⟦b⟧))` for all shifts. -/
def TensorBijectiveShifts (X Y : C) : Prop :=
  ∀ a b : ℤ, Φ.TensorBijective hΦ (X⟦a⟧) (Y⟦b⟧)

omit [HasZeroObject C] [Pretriangulated C] [HasZeroObject D] [Pretriangulated D]
  [Φ.IsTriangulated] [Module.Flat F F'] in
lemma tensorBijectiveShifts_of_forall {X Y : C}
    (h : ∀ n : ℤ, Φ.TensorBijective hΦ X (Y⟦n⟧)) : Φ.TensorBijectiveShifts hΦ X Y :=
  fun a b ↦ ((h (b - a)).shift a).of_iso (Iso.refl _)
    ((shiftFunctorAdd' C (b - a) a b (by lia)).app Y).symm

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Φ.CommShift ℤ] [Φ.IsTriangulated] [Module.Flat F F'] [∀ n : ℤ, (shiftFunctor C n).Linear F]
  [∀ n : ℤ, (shiftFunctor D n).Linear F'] in
lemma TensorBijectiveShifts.tensorBijective {X Y : C} (h : Φ.TensorBijectiveShifts hΦ X Y) :
    Φ.TensorBijective hΦ X Y :=
  (h 0 0).of_iso ((shiftFunctorZero C ℤ).app X) ((shiftFunctorZero C ℤ).app Y)

variable (Φ hΦ) in
/-- For fixed `X`, the objects `Y` with `Φ.TensorBijectiveShifts hΦ X Y`. -/
def tensorBijectiveShiftsRight (X : C) : ObjectProperty C :=
  fun Y ↦ Φ.TensorBijectiveShifts hΦ X Y

variable (Φ hΦ) in
/-- For fixed `Y`, the objects `X` with `Φ.TensorBijectiveShifts hΦ X Y`. -/
def tensorBijectiveShiftsLeft (Y : C) : ObjectProperty C :=
  fun X ↦ Φ.TensorBijectiveShifts hΦ X Y

instance (X : C) : (Φ.tensorBijectiveShiftsRight hΦ X).IsClosedUnderIsomorphisms where
  of_iso e h a b := (h a b).of_iso (Iso.refl _) ((shiftFunctor C b).mapIso e)

instance (Y : C) : (Φ.tensorBijectiveShiftsLeft hΦ Y).IsClosedUnderIsomorphisms where
  of_iso e h a b := (h a b).of_iso ((shiftFunctor C a).mapIso e) (Iso.refl _)

instance isTriangulated_tensorBijectiveShiftsRight (X : C) :
    (Φ.tensorBijectiveShiftsRight hΦ X).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun _ _ ↦
    TensorBijective.of_isZero_right ((shiftFunctor C _).map_isZero (isZero_zero C))⟩
  isStableUnderShiftBy c := ⟨fun _ h a b ↦
    (h a (c + b)).of_iso (Iso.refl _) ((shiftFunctorAdd C c b).app _)⟩
  toIsTriangulatedClosed₂ := by
    refine ObjectProperty.IsTriangulatedClosed₂.mk' ?_
    intro T hT h₁ h₃ a b
    have hT' := Triangle.shift_distinguished T hT b
    refine tensorBijective_obj₂_of_triangle (X⟦a⟧) _ hT' ?_ (h₁ a b) (h₃ a b) ?_
    · exact ((h₃ a (b - 1)).of_iso (Iso.refl _)
        ((shiftFunctorAdd' C b (-1) (b - 1) (by lia)).app _)).2
    · exact ((h₁ a (b + 1)).of_iso (Iso.refl _)
        ((shiftFunctorAdd' C b 1 (b + 1) rfl).app _)).1

instance isTriangulated_tensorBijectiveShiftsLeft (Y : C) :
    (Φ.tensorBijectiveShiftsLeft hΦ Y).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun _ _ ↦
    TensorBijective.of_isZero_left ((shiftFunctor C _).map_isZero (isZero_zero C))⟩
  isStableUnderShiftBy c := ⟨fun _ h a b ↦
    (h (c + a) b).of_iso ((shiftFunctorAdd C c a).app _) (Iso.refl _)⟩
  toIsTriangulatedClosed₂ := by
    refine ObjectProperty.IsTriangulatedClosed₂.mk' ?_
    intro T hT h₁ h₃ a b
    have hT' := Triangle.shift_distinguished T hT a
    refine tensorBijective_obj₂_of_triangle' (Y⟦b⟧) _ hT' ?_ (h₃ a b) (h₁ a b) ?_
    · exact ((h₁ (a + 1) b).of_iso
        ((shiftFunctorAdd' C a 1 (a + 1) rfl).app _) (Iso.refl _)).2
    · exact ((h₃ (a - 1) b).of_iso
        ((shiftFunctorAdd' C a (-1) (a - 1) (by lia)).app _) (Iso.refl _)).1

omit [∀ n : ℤ, (shiftFunctor C n).Linear F] [∀ n : ℤ, (shiftFunctor D n).Linear F'] in
/-- If the objects satisfying `S` lie in every triangulated subcategory, closed under
isomorphisms, containing `G`, and `Φ` induces bijections `F' ⊗ Hom(G⟦a⟧, G⟦b⟧) ≃ Hom(Φ G⟦a⟧,
Φ G⟦b⟧)`, then `F' ⊗ Hom(X, Y) ≃ Hom(Φ X, Φ Y)` for all `X`, `Y` satisfying `S`. -/
lemma tensorBijective_of_generator {G : C} {S : ObjectProperty C}
    (hG : ∀ (P : ObjectProperty C) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms], P G →
      ∀ X, S X → P X)
    (hGG : Φ.TensorBijectiveShifts hΦ G G) {X Y : C} (hX : S X) (hY : S Y) :
    Φ.TensorBijective hΦ X Y :=
  (hG (Φ.tensorBijectiveShiftsLeft hΦ Y)
    (hG (Φ.tensorBijectiveShiftsRight hΦ G) hGG Y hY) X hX).tensorBijective

end Shift

end Functor

end CategoryTheory
