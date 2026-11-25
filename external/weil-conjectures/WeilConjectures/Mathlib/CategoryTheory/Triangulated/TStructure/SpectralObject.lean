/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# t-exact functors and the spectral objects attached to t-structures

Let `F : C ⥤ D` be a triangulated functor between triangulated categories equipped with
t-structures `t₁` and `t₂`. We say that `F` is *t-exact* (`Functor.IsTExact`) if it preserves
the objects which are `≤ n` and the objects which are `≥ n` for all `n : ℤ`. A t-exact functor
commutes with the truncation functors (`Functor.eTruncLTIso`, `Functor.eTruncGEIso`), compatibly
with the connecting homomorphisms of the truncation triangles
(`Functor.eTruncGEδLT_comm`). As a consequence, the image under `F` of the spectral object
`t₁.spectralObject X` consisting of all the truncations of `X` identifies to the spectral object
`t₂.spectralObject (F.obj X)` (`Functor.mapTriangulatedSpectralObjectIso`), naturally in `X`.

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated ComposableArrows Triangulated

variable {C D : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (t₁ : TStructure C) (t₂ : TStructure D)

namespace Functor

/-- A functor `F : C ⥤ D` between categories equipped with t-structures `t₁` and `t₂` is
*t-exact* if it sends objects which are `≤ n` (resp. `≥ n`) for `t₁` to objects which are
`≤ n` (resp. `≥ n`) for `t₂`. -/
class IsTExact (F : C ⥤ D) : Prop where
  isLE (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n
  isGE (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

variable (F : C ⥤ D)

namespace IsTExact

variable [F.IsTExact t₁ t₂]

include t₂ in
lemma isLE_obj (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n :=
  IsTExact.isLE (t₁ := t₁) (t₂ := t₂) (F := F) X n

include t₁ in
lemma isGE_obj (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n :=
  IsTExact.isGE (t₁ := t₁) (t₂ := t₂) (F := F) X n

end IsTExact

variable [CategoryTheory.IsTriangulated D]
  [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t₁ t₂]

section

variable {t₁ t₂}

omit [CategoryTheory.IsTriangulated D] in
lemma isIso_eTruncLTι_app_map_eTruncLT_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    refine ⟨0, (Functor.zero_obj _).eq_of_src _ _, ?_⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _
  | coe n =>
    have := IsTExact.isLE_obj t₁ t₂ F ((t₁.truncLT n).obj X) (n - 1)
    exact (t₂.isLE_iff_isIso_truncLTι_app (n - 1) n (by lia) _).1 this
  | top => dsimp; infer_instance

lemma isIso_eTruncLT_obj_map_map_eTruncLTι_app (i : EInt) (X : C) :
    IsIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X))) := by
  induction i using WithBotTop.rec with
  | bot =>
    exact ⟨0, (Functor.zero_obj _).eq_of_src _ _, (Functor.zero_obj _).eq_of_src _ _⟩
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact t₂.isIso₁_truncLT_map_of_isGE (F.mapTriangle.obj ((t₁.triangleLTGE n).obj X))
      (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)) n this
  | top => dsimp; infer_instance

omit [CategoryTheory.IsTriangulated D] in
lemma isIso_eTruncGEπ_app_map_eTruncGE_obj_obj (i : EInt) (X : C) :
    IsIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe n =>
    have := IsTExact.isGE_obj t₁ t₂ F ((t₁.truncGE n).obj X) n
    exact (t₂.isGE_iff_isIso_truncGEπ_app n _).1 this
  | top =>
    refine ⟨0, ?_, (Functor.zero_obj _).eq_of_src _ _⟩
    exact (F.map_isZero (Functor.zero_obj X)).eq_of_src _ _

lemma isIso_eTruncGE_obj_map_map_eTruncGEπ_app (i : EInt) (X : C) :
    IsIso ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X))) := by
  induction i using WithBotTop.rec with
  | bot => dsimp; infer_instance
  | coe n =>
    have := IsTExact.isLE_obj t₁ t₂ F ((t₁.truncLT n).obj X) (n - 1)
    exact t₂.isIso₂_truncGE_map_of_isLE (F.mapTriangle.obj ((t₁.triangleLTGE n).obj X))
      (F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)) (n - 1) n (by lia) this
  | top =>
    exact ⟨0, (Functor.zero_obj _).eq_of_src _ _, (Functor.zero_obj _).eq_of_src _ _⟩

end

/-- The component at `X` of `Functor.eTruncLTIso`. -/
noncomputable def eTruncLTIsoApp (i : EInt) (X : C) :
    F.obj ((t₁.eTruncLT.obj i).obj X) ≅ (t₂.eTruncLT.obj i).obj (F.obj X) :=
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  have := F.isIso_eTruncLT_obj_map_map_eTruncLTι_app (t₁ := t₁) (t₂ := t₂) i X
  (asIso ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)))).symm ≪≫
    asIso ((t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X)))

@[reassoc]
lemma eTruncLTι_app_eTruncLTIsoApp_hom (i : EInt) (X : C) :
    (t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
      (F.eTruncLTIsoApp t₁ t₂ i X).hom =
      (t₂.eTruncLT.obj i).map (F.map ((t₁.eTruncLTι i).app X)) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  simp [eTruncLTIsoApp]

@[reassoc (attr := simp)]
lemma eTruncLTIsoApp_hom_eTruncLTι_app (i : EInt) (X : C) :
    (F.eTruncLTIsoApp t₁ t₂ i X).hom ≫ (t₂.eTruncLTι i).app (F.obj X) =
      F.map ((t₁.eTruncLTι i).app X) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
    reassoc_of% (F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂ i X)]
  exact (t₂.eTruncLTι i).naturality _

/-- The component at `X` of `Functor.eTruncGEIso`. -/
noncomputable def eTruncGEIsoApp (i : EInt) (X : C) :
    F.obj ((t₁.eTruncGE.obj i).obj X) ≅ (t₂.eTruncGE.obj i).obj (F.obj X) :=
  have := F.isIso_eTruncGEπ_app_map_eTruncGE_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  asIso ((t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X))) ≪≫
    (asIso ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)))).symm

@[reassoc]
lemma eTruncGEIsoApp_hom_eTruncGE_map (i : EInt) (X : C) :
    (F.eTruncGEIsoApp t₁ t₂ i X).hom ≫ (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)) =
      (t₂.eTruncGEπ i).app (F.obj ((t₁.eTruncGE.obj i).obj X)) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  simp [eTruncGEIsoApp]

@[reassoc (attr := simp)]
lemma eTruncGEπ_app_eTruncGEIsoApp_hom (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEπ i).app X) ≫ (F.eTruncGEIsoApp t₁ t₂ i X).hom =
      (t₂.eTruncGEπ i).app (F.obj X) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i X
  rw [← cancel_mono ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X))), Category.assoc,
    F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂ i X]
  exact (t₂.eTruncGEπ i).naturality _

/-- A t-exact functor commutes with the truncation functors `t.eTruncLT.obj i`. -/
noncomputable def eTruncLTIso (i : EInt) :
    t₁.eTruncLT.obj i ⋙ F ≅ F ⋙ t₂.eTruncLT.obj i :=
  NatIso.ofComponents (F.eTruncLTIsoApp t₁ t₂ i) (fun {X Y} f ↦ by
    have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
    rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
      F.eTruncLTι_app_eTruncLTIsoApp_hom_assoc t₁ t₂]
    have h := (t₂.eTruncLTι i).naturality (F.map ((t₁.eTruncLT.obj i).map f))
    dsimp at h ⊢
    rw [← reassoc_of% h, F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    exact (t₁.eTruncLTι i).naturality f)

@[simp]
lemma eTruncLTIso_hom_app (i : EInt) (X : C) :
    (F.eTruncLTIso t₁ t₂ i).hom.app X = (F.eTruncLTIsoApp t₁ t₂ i X).hom := rfl

/-- A t-exact functor commutes with the truncation functors `t.eTruncGE.obj i`. -/
noncomputable def eTruncGEIso (i : EInt) :
    t₁.eTruncGE.obj i ⋙ F ≅ F ⋙ t₂.eTruncGE.obj i :=
  NatIso.ofComponents (F.eTruncGEIsoApp t₁ t₂ i) (fun {X Y} f ↦ by
    have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) i Y
    rw [← cancel_mono ((t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app Y))),
      Category.assoc, F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂]
    have h := (t₂.eTruncGEπ i).naturality (F.map ((t₁.eTruncGE.obj i).map f))
    dsimp at h ⊢
    rw [h, Category.assoc, ← Functor.map_comp, ← F.map_comp, ← t₁.eTruncGEπ_naturality,
      F.map_comp, Functor.map_comp, F.eTruncGEIsoApp_hom_eTruncGE_map_assoc t₁ t₂])

@[simp]
lemma eTruncGEIso_hom_app (i : EInt) (X : C) :
    (F.eTruncGEIso t₁ t₂ i).hom.app X = (F.eTruncGEIsoApp t₁ t₂ i X).hom := rfl

@[reassoc]
lemma eTruncLT_map_app_eTruncLTIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncLT.map f).app X) ≫ (F.eTruncLTIso t₁ t₂ j).hom.app X =
      (F.eTruncLTIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncLT.map f).app (F.obj X) := by
  have := F.isIso_eTruncLTι_app_map_eTruncLT_obj_obj (t₁ := t₁) (t₂ := t₂) i X
  simp only [eTruncLTIso_hom_app]
  rw [← cancel_epi ((t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X))),
    F.eTruncLTι_app_eTruncLTIsoApp_hom_assoc t₁ t₂]
  have h : (t₂.eTruncLTι i).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
      F.map ((t₁.eTruncLT.map f).app X) =
      (t₂.eTruncLT.map f).app (F.obj ((t₁.eTruncLT.obj i).obj X)) ≫
        (t₂.eTruncLT.obj j).map (F.map ((t₁.eTruncLT.map f).app X)) ≫
        (t₂.eTruncLTι j).app (F.obj ((t₁.eTruncLT.obj j).obj X)) := by
    have h₁ := (t₂.eTruncLTι j).naturality (F.map ((t₁.eTruncLT.map f).app X))
    dsimp at h₁
    rw [h₁, t₂.eTruncLT_map_app_eTruncLTι_app_assoc]
  rw [reassoc_of% h, F.eTruncLTι_app_eTruncLTIsoApp_hom t₁ t₂, ← Functor.map_comp, ← F.map_comp,
    t₁.eTruncLT_map_app_eTruncLTι_app]
  exact ((t₂.eTruncLT.map f).naturality _).symm

@[reassoc]
lemma eTruncGE_map_app_eTruncGEIso_hom_app {i j : EInt} (f : i ⟶ j) (X : C) :
    F.map ((t₁.eTruncGE.map f).app X) ≫ (F.eTruncGEIso t₁ t₂ j).hom.app X =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGE.map f).app (F.obj X) := by
  have := F.isIso_eTruncGE_obj_map_map_eTruncGEπ_app (t₁ := t₁) (t₂ := t₂) j X
  simp only [eTruncGEIso_hom_app]
  rw [← cancel_mono ((t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X))), Category.assoc,
    Category.assoc, F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂]
  have h : (t₂.eTruncGE.map f).app (F.obj X) ≫
      (t₂.eTruncGE.obj j).map (F.map ((t₁.eTruncGEπ j).app X)) =
      (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGEπ i).app X)) ≫
        (t₂.eTruncGE.obj i).map (F.map ((t₁.eTruncGE.map f).app X)) ≫
        (t₂.eTruncGE.map f).app (F.obj ((t₁.eTruncGE.obj j).obj X)) := by
    rw [← Functor.map_comp_assoc, ← F.map_comp, t₁.eTruncGEπ_app_eTruncGE_map_app]
    exact ((t₂.eTruncGE.map f).naturality _).symm
  rw [h, reassoc_of% (F.eTruncGEIsoApp_hom_eTruncGE_map t₁ t₂ i X)]
  have h₂ := (t₂.eTruncGEπ i).naturality (F.map ((t₁.eTruncGE.map f).app X))
  dsimp at h₂
  rw [← reassoc_of% h₂, t₂.eTruncGEπ_app_eTruncGE_map_app]

/-- A t-exact triangulated functor commutes with the connecting homomorphisms of the truncation
triangles. -/
@[reassoc]
lemma eTruncGEδLT_comm (i : EInt) (X : C) :
    F.map ((t₁.eTruncGEδLT.app i).app X) ≫ (F.commShiftIso (1 : ℤ)).hom.app _ ≫
        ((F.eTruncLTIso t₁ t₂ i).hom.app X)⟦(1 : ℤ)⟧' =
      (F.eTruncGEIso t₁ t₂ i).hom.app X ≫ (t₂.eTruncGEδLT.app i).app (F.obj X) := by
  induction i using WithBotTop.rec with
  | bot => simp [TStructure.eTruncGEδLT]
  | top => simp [TStructure.eTruncGEδLT]
  | coe n =>
    let T₁ := F.mapTriangle.obj ((t₁.triangleLTGE n).obj X)
    have hT₁ : T₁ ∈ distTriang D := F.map_distinguished _ (t₁.triangleLTGE_distinguished n X)
    have hT₂ := t₂.triangleLTGE_distinguished n (F.obj X)
    have h₁ : t₂.IsLE T₁.obj₁ (n - 1) := IsTExact.isLE_obj t₁ t₂ F _ _
    have h₃ : t₂.IsGE T₁.obj₃ n := IsTExact.isGE_obj t₁ t₂ F _ _
    have : t₂.IsLE (T₁.obj₁⟦(1 : ℤ)⟧) (n - 2) := t₂.isLE_shift _ (n - 1) 1 (n - 2) (by lia)
    obtain ⟨φ, hφ⟩ := t₂.triangle_map_exists hT₁ hT₂ (𝟙 _) (n - 1) n h₁ inferInstance
    have e₁ : φ.hom₁ = (F.eTruncLTIsoApp t₁ t₂ n X).hom := by
      apply t₂.to_truncLT_obj_ext
      have := φ.comm₁
      rw [hφ, Category.comp_id] at this
      exact this.symm.trans (F.eTruncLTIsoApp_hom_eTruncLTι_app t₁ t₂ n X).symm
    let ψ : T₁.obj₃ ⟶ ((t₂.triangleLTGE n).obj (F.obj X)).obj₃ :=
      (F.eTruncGEIsoApp t₁ t₂ n X).hom
    have e₃ : φ.hom₃ = ψ := by
      rw [← sub_eq_zero]
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T₁ hT₁ (φ.hom₃ - ψ) (by
        have := φ.comm₂
        rw [hφ, Category.id_comp] at this
        rw [Preadditive.comp_sub, this, sub_eq_zero]
        exact (F.eTruncGEπ_app_eTruncGEIsoApp_hom t₁ t₂ n X).symm)
      rw [hg, t₂.zero_of_isLE_of_isGE g (n - 2) n (by lia) inferInstance inferInstance,
        comp_zero]
    have := φ.comm₃
    rw [e₁, e₃] at this
    exact (Category.assoc _ _ _).symm.trans this

variable [CategoryTheory.IsTriangulated C]

/-- The image under a t-exact functor `F` of `τ_{≥ a} τ_{< b} X` is `τ_{≥ a} τ_{< b} F(X)`. -/
noncomputable def eTruncGELTIsoApp (a b : EInt) (X : C) :
    F.obj ((t₁.eTruncGE.obj a).obj ((t₁.eTruncLT.obj b).obj X)) ≅
      (t₂.eTruncGE.obj a).obj ((t₂.eTruncLT.obj b).obj (F.obj X)) :=
  F.eTruncGEIsoApp t₁ t₂ a ((t₁.eTruncLT.obj b).obj X) ≪≫
    (t₂.eTruncGE.obj a).mapIso (F.eTruncLTIsoApp t₁ t₂ b X)

omit [CategoryTheory.IsTriangulated C] in
@[reassoc]
lemma eTruncGELTIsoApp_hom_naturality {a b a' b' : EInt} (ha : a ⟶ a') (hb : b ⟶ b') (X : C) :
    F.map ((t₁.eTruncGE.map ha).app ((t₁.eTruncLT.obj b).obj X)) ≫
        F.map ((t₁.eTruncGE.obj a').map ((t₁.eTruncLT.map hb).app X)) ≫
        (F.eTruncGELTIsoApp t₁ t₂ a' b' X).hom =
      (F.eTruncGELTIsoApp t₁ t₂ a b X).hom ≫
        (t₂.eTruncGE.map ha).app ((t₂.eTruncLT.obj b).obj (F.obj X)) ≫
        (t₂.eTruncGE.obj a').map ((t₂.eTruncLT.map hb).app (F.obj X)) := by
  have h₁ := (F.eTruncGEIso t₁ t₂ a').hom.naturality ((t₁.eTruncLT.map hb).app X)
  simp only [Functor.comp_map, eTruncGEIso_hom_app] at h₁
  have h₂ := F.eTruncGE_map_app_eTruncGEIso_hom_app t₁ t₂ ha ((t₁.eTruncLT.obj b).obj X)
  have h₃ := F.eTruncLT_map_app_eTruncLTIso_hom_app t₁ t₂ hb X
  simp only [eTruncGEIso_hom_app, eTruncLTIso_hom_app] at h₂ h₃
  simp only [eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← Functor.map_comp, h₃, Functor.map_comp,
    ← NatTrans.naturality_assoc]
  rfl

lemma eTruncGELTIsoApp_δ (a b c : EInt) (X : C) :
    F.map ((t₁.eTruncGEδLT.app b).app ((t₁.eTruncLT.obj c).obj X) ≫
        ((t₁.eTruncLT.obj b).map ((t₁.eTruncGEπ a).app ((t₁.eTruncLT.obj c).obj X)))⟦(1 : ℤ)⟧' ≫
        ((t₁.eTruncLTGEIsoGELT a b).hom.app ((t₁.eTruncLT.obj c).obj X))⟦(1 : ℤ)⟧' ≫
        ((t₁.eTruncGE.obj a).map ((t₁.eTruncLT.obj b).map
          ((t₁.eTruncLTι c).app X)))⟦(1 : ℤ)⟧') ≫
      (F.commShiftIso (1 : ℤ)).hom.app _ ≫ ((F.eTruncGELTIsoApp t₁ t₂ a b X).hom)⟦(1 : ℤ)⟧' =
    (F.eTruncGELTIsoApp t₁ t₂ b c X).hom ≫
      (t₂.eTruncGEδLT.app b).app ((t₂.eTruncLT.obj c).obj (F.obj X)) ≫
        ((t₂.eTruncLT.obj b).map
          ((t₂.eTruncGEπ a).app ((t₂.eTruncLT.obj c).obj (F.obj X))))⟦(1 : ℤ)⟧' ≫
        ((t₂.eTruncLTGEIsoGELT a b).hom.app ((t₂.eTruncLT.obj c).obj (F.obj X)))⟦(1 : ℤ)⟧' ≫
        ((t₂.eTruncGE.obj a).map ((t₂.eTruncLT.obj b).map
          ((t₂.eTruncLTι c).app (F.obj X))))⟦(1 : ℤ)⟧' := by
  set Y := (t₁.eTruncLT.obj c).obj X
  have inner : F.map ((t₁.eTruncLT.obj b).map ((t₁.eTruncGEπ a).app Y)) ≫
      F.map ((t₁.eTruncLTGEIsoGELT a b).hom.app Y) ≫
      F.map ((t₁.eTruncGE.obj a).map ((t₁.eTruncLT.obj b).map ((t₁.eTruncLTι c).app X))) ≫
      (F.eTruncGELTIsoApp t₁ t₂ a b X).hom =
      (F.eTruncLTIsoApp t₁ t₂ b Y).hom ≫
        (t₂.eTruncLT.obj b).map (F.eTruncLTIsoApp t₁ t₂ c X).hom ≫
        (t₂.eTruncLT.obj b).map ((t₂.eTruncGEπ a).app ((t₂.eTruncLT.obj c).obj (F.obj X))) ≫
        (t₂.eTruncLTGEIsoGELT a b).hom.app ((t₂.eTruncLT.obj c).obj (F.obj X)) ≫
        (t₂.eTruncGE.obj a).map ((t₂.eTruncLT.obj b).map ((t₂.eTruncLTι c).app (F.obj X))) := by
    have h₁ := t₁.eTruncLT_map_eTruncGEπ_app_eTruncLTGEIsoGELT_hom_app a b Y
    have h₃ := (F.eTruncLTIso t₁ t₂ b).hom.naturality ((t₁.eTruncLTι c).app X)
    simp only [Functor.comp_map, eTruncLTIso_hom_app] at h₃
    rw [t₂.eTruncLT_map_eTruncGEπ_app_eTruncLTGEIsoGELT_hom_app_assoc,
      ← F.map_comp_assoc, h₁, ← F.map_comp_assoc, t₁.eTruncGEπ_naturality]
    simp only [eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom, F.map_comp,
      Category.assoc]
    erw [F.eTruncGEπ_app_eTruncGEIsoApp_hom_assoc t₁ t₂ a ((t₁.eTruncLT.obj b).obj X)]
    rw [t₂.eTruncGEπ_naturality, t₂.eTruncGEπ_naturality,
      ← Functor.map_comp_assoc (t₂.eTruncLT.obj b),
      F.eTruncLTIsoApp_hom_eTruncLTι_app t₁ t₂ c X]
    erw [← reassoc_of% h₃]
    rfl
  have inner' := congrArg (fun g ↦ (shiftFunctor D (1 : ℤ)).map g) inner
  simp only [Functor.map_comp] at inner'
  have hδ := F.eTruncGEδLT_comm t₁ t₂ b Y
  simp only [eTruncLTIso_hom_app, eTruncGEIso_hom_app] at hδ
  have hδ' := (t₂.eTruncGEδLT.app b).naturality (F.eTruncLTIsoApp t₁ t₂ c X).hom
  simp only [F.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc]
  rw [inner', reassoc_of% hδ]
  simp only [eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hδ']
  rfl

omit [CategoryTheory.IsTriangulated C] in
@[reassoc]
lemma eTruncGELTIsoApp_hom_naturality_obj (a b : EInt) {X Y : C} (f : X ⟶ Y) :
    F.map ((t₁.eTruncGE.obj a).map ((t₁.eTruncLT.obj b).map f)) ≫
        (F.eTruncGELTIsoApp t₁ t₂ a b Y).hom =
      (F.eTruncGELTIsoApp t₁ t₂ a b X).hom ≫
        (t₂.eTruncGE.obj a).map ((t₂.eTruncLT.obj b).map (F.map f)) := by
  have h₁ := (F.eTruncGEIso t₁ t₂ a).hom.naturality ((t₁.eTruncLT.obj b).map f)
  have h₂ := (F.eTruncLTIso t₁ t₂ b).hom.naturality f
  simp only [Functor.comp_map, eTruncGEIso_hom_app, eTruncLTIso_hom_app] at h₁ h₂
  simp only [eTruncGELTIsoApp, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h₁, ← Functor.map_comp, ← Functor.map_comp, h₂]

/-- The image under a t-exact triangulated functor `F` of the spectral object
`t₁.spectralObject X` of all the truncations of `X` is the spectral object
`t₂.spectralObject (F.obj X)` of all the truncations of `F.obj X`. -/
noncomputable def mapTriangulatedSpectralObjectObjIso (X : C) :
    (t₁.spectralObject X).mapTriangulatedFunctor F ≅ t₂.spectralObject (F.obj X) :=
  Triangulated.SpectralObject.isoMk
    (NatIso.ofComponents (fun D ↦ F.eTruncGELTIsoApp t₁ t₂ (D.obj 0) (D.obj 1) X)
      (fun {D D'} φ ↦ by
        have := F.eTruncGELTIsoApp_hom_naturality t₁ t₂ (φ.app 0) (φ.app 1) X
        rw [← F.map_comp_assoc] at this
        change F.map ((t₁.ω₁.map φ).app X) ≫ _ = _ ≫ (t₂.ω₁.map φ).app (F.obj X)
        rw [TStructure.ω₁_map, TStructure.ω₁_map, NatTrans.hcomp_app, NatTrans.hcomp_app]
        exact this))
    (fun {i j k} f g ↦ by
      have := F.eTruncGELTIsoApp_δ t₁ t₂ i j k X
      change (F.map ((t₁.ω₁δ i j k (leOfHom f) (leOfHom g)).app X) ≫
          (F.commShiftIso (1 : ℤ)).hom.app _) ≫ ((F.eTruncGELTIsoApp t₁ t₂ i j X).hom)⟦(1 : ℤ)⟧' =
        (F.eTruncGELTIsoApp t₁ t₂ j k X).hom ≫ (t₂.ω₁δ i j k (leOfHom f) (leOfHom g)).app (F.obj X)
      rw [TStructure.ω₁δ_app, TStructure.ω₁δ_app, Category.assoc]
      exact this)

@[simp]
lemma mapTriangulatedSpectralObjectObjIso_hom_hom_app (X : C) (D : ComposableArrows EInt 1) :
    (F.mapTriangulatedSpectralObjectObjIso t₁ t₂ X).hom.hom.app D =
      (F.eTruncGELTIsoApp t₁ t₂ (D.obj 0) (D.obj 1) X).hom := by
  simp [mapTriangulatedSpectralObjectObjIso]

/-- A t-exact triangulated functor `F` commutes with the formation of the spectral objects
consisting of all the truncations of objects. -/
noncomputable def mapTriangulatedSpectralObjectIso :
    t₁.spectralObjectFunctor ⋙ F.mapTriangulatedSpectralObject EInt ≅
      F ⋙ t₂.spectralObjectFunctor :=
  NatIso.ofComponents (F.mapTriangulatedSpectralObjectObjIso t₁ t₂) (fun {X Y} f ↦ by
    ext D
    have := F.eTruncGELTIsoApp_hom_naturality_obj t₁ t₂ (D.obj 0) (D.obj 1) f
    change F.map ((t₁.eTruncGE.obj (D.obj 0)).map ((t₁.eTruncLT.obj (D.obj 1)).map f)) ≫
        (F.eTruncGELTIsoApp t₁ t₂ (D.obj 0) (D.obj 1) Y).hom =
      (F.eTruncGELTIsoApp t₁ t₂ (D.obj 0) (D.obj 1) X).hom ≫
        (t₂.eTruncGE.obj (D.obj 0)).map ((t₂.eTruncLT.obj (D.obj 1)).map (F.map f))
    exact this)

@[simp]
lemma mapTriangulatedSpectralObjectIso_hom_app_hom_app (X : C) (D : ComposableArrows EInt 1) :
    ((F.mapTriangulatedSpectralObjectIso t₁ t₂).hom.app X).hom.app D =
      (F.eTruncGELTIsoApp t₁ t₂ (D.obj 0) (D.obj 1) X).hom := by
  simp [mapTriangulatedSpectralObjectIso]

end Functor

end CategoryTheory
