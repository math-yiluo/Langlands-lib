/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-!
# Exact functors and `Ext`-classes composed with morphisms on both sides

For morphisms `a : X' ⟶ X`, `b : Y ⟶ Y'` and `y ∈ Extⁿ(X, Y)`, write
`CategoryTheory.Abelian.Ext.mk₀CompMk₀ a y b = a ∘ y ∘ b ∈ Extⁿ(X', Y')`. This file records how
these composites behave under composition and under pushforward along exact functors, and
deduces the comparison of two "pullback" operations on `Ext`-classes intertwined by an exact
functor (`CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀CompMk₀_of_iso`): if `τ : G₂ ⋙ G_B ≅
G_A ⋙ G₂`, then pushing `a ∘ G₂(x) ∘ b` forward along `G_B` is `G₂` of the conjugate
`α⁻¹ ∘ G_A(x) ∘ α`, up to explicit morphisms on both sides.
-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory.Abelian.Ext

open Limits

section Comp

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The class `a ∘ y ∘ b ∈ Extⁿ(X', Y')` for `y ∈ Extⁿ(X, Y)` and morphisms `a : X' ⟶ X`,
`b : Y ⟶ Y'`. -/
noncomputable def mk₀CompMk₀ {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') : Ext.{w} X' Y' n :=
  (mk₀ a).comp (y.comp (mk₀ b) (add_zero n)) (zero_add n)

lemma mk₀CompMk₀_mk₀CompMk₀ {X'' X' X Y Y' Y'' : C} {n : ℕ} (a' : X'' ⟶ X') (a : X' ⟶ X)
    (y : Ext.{w} X Y n) (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    mk₀CompMk₀ a' (mk₀CompMk₀ a y b) b' = mk₀CompMk₀ (a' ≫ a) y (b ≫ b') := by
  simp only [mk₀CompMk₀, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, mk₀_comp_mk₀_assoc]

@[simp]
lemma mk₀CompMk₀_id {X Y : C} {n : ℕ} (y : Ext.{w} X Y n) : mk₀CompMk₀ (𝟙 X) y (𝟙 Y) = y := by
  simp [mk₀CompMk₀]

lemma mk₀CompMk₀_add {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y y' : Ext.{w} X Y n)
    (b : Y ⟶ Y') : mk₀CompMk₀ a (y + y') b = mk₀CompMk₀ a y b + mk₀CompMk₀ a y' b := by
  simp [mk₀CompMk₀, add_comp, comp_add]


lemma mk₀_comp_mk₀CompMk₀ {X'' X' X Y Y' : C} {n : ℕ} (a' : X'' ⟶ X') (a : X' ⟶ X)
    (y : Ext.{w} X Y n) (b : Y ⟶ Y') :
    (mk₀ a').comp (mk₀CompMk₀ a y b) (zero_add n) = mk₀CompMk₀ (a' ≫ a) y b := by
  simp [mk₀CompMk₀]

lemma mk₀CompMk₀_comp_mk₀ {X' X Y Y' Y'' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    (mk₀CompMk₀ a y b).comp (mk₀ b') (add_zero n) = mk₀CompMk₀ a y (b ≫ b') := by
  simp [mk₀CompMk₀, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀]

lemma mk₀_comp_comp_mk₀ {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') :
    ((mk₀ a).comp y (zero_add n)).comp (mk₀ b) (add_zero n) = mk₀CompMk₀ a y b :=
  comp_assoc_of_third_deg_zero _ _ _ _

lemma mk₀CompMk₀_comp_mk₀_right {X' X Y Y' Y'' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') (b' : Y' ⟶ Y'') :
    mk₀CompMk₀ a (y.comp (mk₀ b) (add_zero n)) b' = mk₀CompMk₀ a y (b ≫ b') := by
  simp [mk₀CompMk₀, mk₀_comp_mk₀]

end Comp

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]

lemma mapExactFunctor_mk₀CompMk₀ (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {X' X Y Y' : C} {n : ℕ} (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') :
    (mk₀CompMk₀ a y b).mapExactFunctor F =
      mk₀CompMk₀ (F.map a) (y.mapExactFunctor F) (F.map b) := by
  simp only [mk₀CompMk₀, mapExactFunctor_comp, mapExactFunctor_mk₀]

/-- `mapExactFunctor_eq_of_iso`, in terms of `mk₀CompMk₀`. -/
lemma mapExactFunctor_eq_mk₀CompMk₀_of_iso [EnoughInjectives C] {G G' : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G'.Additive]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] (τ : G ≅ G') {A B : C} {n : ℕ}
    (x : Ext.{w} A B n) :
    x.mapExactFunctor G' = mk₀CompMk₀ (τ.inv.app A) (x.mapExactFunctor G) (τ.hom.app B) :=
  mapExactFunctor_eq_of_iso τ x

/-- **Pullbacks of `Ext`-classes intertwined by an exact functor.** Let `G₂ : C ⥤ D`,
`G_C : C ⥤ C`, `G_D : D ⥤ D` be exact and `τ : G₂ ⋙ G_D ≅ G_C ⋙ G₂`. For `x ∈ Extⁿ(P, P)`,
pushing `ζ ∘ G_D(U ∘ G₂(x) ∘ V) ∘ κ` is `L ∘ G₂(α⁻¹ ∘ G_C(x) ∘ α) ∘ R` for explicit `L`, `R`. -/
lemma mapExactFunctor_mk₀CompMk₀_of_iso [EnoughInjectives C] (G₂ : C ⥤ D) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (GC : C ⥤ C) [GC.Additive]
    [PreservesFiniteLimits GC] [PreservesFiniteColimits GC] (GD : D ⥤ D) [GD.Additive]
    [PreservesFiniteLimits GD] [PreservesFiniteColimits GD]
    [PreservesFiniteLimits (G₂ ⋙ GD)] [PreservesFiniteColimits (G₂ ⋙ GD)]
    [PreservesFiniteLimits (GC ⋙ G₂)] [PreservesFiniteColimits (GC ⋙ G₂)]
    (τ : G₂ ⋙ GD ≅ GC ⋙ G₂) {P : C} {I J : D} (U : I ⟶ G₂.obj P) (V : G₂.obj P ⟶ J)
    (ζ : I ⟶ GD.obj I) (κ : GD.obj J ⟶ J) (α : GC.obj P ≅ P) {n : ℕ} (x : Ext.{w} P P n) :
    mk₀CompMk₀ ζ ((mk₀CompMk₀ U (x.mapExactFunctor G₂) V).mapExactFunctor GD) κ =
      mk₀CompMk₀ (ζ ≫ GD.map U ≫ τ.hom.app P ≫ G₂.map α.hom)
        ((mk₀CompMk₀ α.inv (x.mapExactFunctor GC) α.hom).mapExactFunctor G₂)
        (G₂.map α.inv ≫ τ.inv.app P ≫ GD.map V ≫ κ) := by
  rw [mapExactFunctor_mk₀CompMk₀, mapExactFunctor_mk₀CompMk₀, mapExactFunctor_mapExactFunctor,
    mapExactFunctor_mapExactFunctor (G₁ := GC), mapExactFunctor_eq_mk₀CompMk₀_of_iso τ.symm]
  simp only [mk₀CompMk₀_mk₀CompMk₀]
  congr 1 <;> simp [← Functor.map_comp, ← Functor.map_comp_assoc]

section Scalar

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma mk₀_zsmul {X Y : C} (k : ℤ) (f : X ⟶ Y) : mk₀ (k • f) = k • (mk₀ f : Ext.{w} X Y 0) :=
  map_zsmul (AddMonoidHom.mk' (mk₀ (X := X) (Y := Y)) mk₀_add) k f

lemma comp_zsmul {X Y Z : C} {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) (k : ℤ) : α.comp (k • β) h = k • α.comp β h :=
  map_zsmul (AddMonoidHom.mk' (fun β : Ext.{w} Y Z b ↦ α.comp β h) fun _ _ ↦ comp_add _ _ _ _) k β

lemma zsmul_comp {X Y Z : C} {a b c : ℕ} (α : Ext.{w} X Y a) (β : Ext.{w} Y Z b)
    (h : a + b = c) (k : ℤ) : (k • α).comp β h = k • α.comp β h :=
  map_zsmul (AddMonoidHom.mk' (fun α : Ext.{w} X Y a ↦ α.comp β h) fun _ _ ↦ add_comp _ _ _ _) k α

lemma mk₀CompMk₀_zsmul_left {X' X Y Y' : C} {n : ℕ} (k : ℤ) (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') : mk₀CompMk₀ (k • a) y b = k • mk₀CompMk₀ a y b := by
  rw [mk₀CompMk₀, mk₀_zsmul, zsmul_comp, mk₀CompMk₀]

lemma mk₀CompMk₀_zsmul_right {X' X Y Y' : C} {n : ℕ} (k : ℤ) (a : X' ⟶ X) (y : Ext.{w} X Y n)
    (b : Y ⟶ Y') : mk₀CompMk₀ a y (k • b) = k • mk₀CompMk₀ a y b := by
  rw [mk₀CompMk₀, mk₀_zsmul, comp_zsmul, comp_zsmul, mk₀CompMk₀]

end Scalar

/-- **Rigidity of `Ext`-classes of an object with scalar endomorphisms.** Let `P` be an object
all of whose endomorphisms are integer multiples of the identity, and `G₂` an exact functor
which is full on the endomorphisms of `P`. If every morphism `I ⟶ G₂ P` factors as `U ≫ G₂ f`
and `V : G₂ P ≅ J`, then for all `L : I ⟶ G₂ P`, `R : G₂ P ⟶ J` there is an integer `c` with
`L ∘ G₂(y) ∘ R = c • (U ∘ G₂(y) ∘ V)` for every class `y ∈ Extⁿ(P, P)`. -/
lemma exists_mk₀CompMk₀_mapExactFunctor_eq_zsmul (G₂ : C ⥤ D) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] {P : C} {I J : D}
    (U : I ⟶ G₂.obj P) (V : G₂.obj P ≅ J) (L : I ⟶ G₂.obj P) (R : G₂.obj P ⟶ J)
    (h0 : ∀ f : P ⟶ P, ∃ k : ℤ, f = k • 𝟙 P)
    (hU : ∀ h : I ⟶ G₂.obj P, ∃ f : P ⟶ P, h = U ≫ G₂.map f)
    (hfull : ∀ h : G₂.obj P ⟶ G₂.obj P, ∃ f : P ⟶ P, h = G₂.map f) :
    ∃ c : ℤ, ∀ (n : ℕ) (y : Ext.{w} P P n),
      mk₀CompMk₀ L (y.mapExactFunctor G₂) R = c • mk₀CompMk₀ U (y.mapExactFunctor G₂) V.hom := by
  obtain ⟨f₁, hf₁⟩ := hU L
  obtain ⟨k, rfl⟩ := h0 f₁
  obtain ⟨f₂, hf₂⟩ := hfull (R ≫ V.inv)
  obtain ⟨r, rfl⟩ := h0 f₂
  have hL : L = k • U := by
    rw [hf₁, Functor.map_zsmul, Functor.map_id, Preadditive.comp_zsmul, Category.comp_id]
  have hR : R = r • V.hom := by
    rw [← Category.comp_id R, ← V.inv_hom_id, ← Category.assoc, hf₂, Functor.map_zsmul,
      Functor.map_id, Preadditive.zsmul_comp, Category.id_comp]
  refine ⟨k * r, fun n y ↦ ?_⟩
  rw [hL, hR, mk₀CompMk₀_zsmul_left, mk₀CompMk₀_zsmul_right, smul_smul]

end CategoryTheory.Abelian.Ext
