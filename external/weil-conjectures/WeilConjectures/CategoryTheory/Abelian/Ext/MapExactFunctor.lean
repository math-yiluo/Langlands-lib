/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-!
# Functoriality of pushing `Ext`-classes along exact functors

Pushing an `Ext`-class forward along exact functors (`CategoryTheory.Abelian.Ext.mapExactFunctor`)
is compatible with composition of functors and, up to conjugation, with natural isomorphisms of
functors. The first two are proved by dimension shifting along an injective presentation,
where the extension classes are compared with
`CategoryTheory.ShortComplex.ShortExact.extClass_naturality`; the comparison with a composite up to
isomorphism is proved in the derived category and needs no injectives.

## Main statements

- `CategoryTheory.Abelian.Ext.mapExactFunctor_mapExactFunctor`: pushing forward along `G₁` and
  then `G₂` is pushing forward along `G₁ ⋙ G₂`.
- `CategoryTheory.Abelian.Ext.mapExactFunctor_eq_of_iso`: pushing forward along isomorphic
  functors gives conjugate classes.
- `CategoryTheory.Abelian.Ext.mapExactFunctor_comp_mk₀_eq`: pushing forward along `G` agrees, up
  to an isomorphism `G ≅ G₁ ⋙ G₂`, with pushing forward along `G₁` and then `G₂`.
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D]
  {E : Type u''} [Category.{v''} E] [Abelian E] [HasExt.{w''} E] [EnoughInjectives C]

/-- Pushing an `Ext`-class forward along `G₁` and then `G₂` is pushing it forward along
`G₁ ⋙ G₂`. -/
lemma mapExactFunctor_mapExactFunctor (G₁ : C ⥤ D) [G₁.Additive] [PreservesFiniteLimits G₁]
    [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive] [PreservesFiniteLimits G₂]
    [PreservesFiniteColimits G₂] [PreservesFiniteLimits (G₁ ⋙ G₂)]
    [PreservesFiniteColimits (G₁ ⋙ G₂)] {A B : C} {n : ℕ} (x : Ext.{w} A B n) :
    (x.mapExactFunctor G₁).mapExactFunctor G₂ = x.mapExactFunctor (G₁ ⋙ G₂) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective A B).2 x
    simp [mapExactFunctor_mk₀]
  | succ n ih =>
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    have h₁ := (hS.map_of_exact G₁).map_of_exact G₂
    have h₂ := hS.map_of_exact (G₁ ⋙ G₂)
    let φ : (S.map G₁).map G₂ ⟶ S.map (G₁ ⋙ G₂) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
        comm₁₂ := by dsimp; rw [Category.id_comp, Category.comp_id]
        comm₂₃ := by dsimp; rw [Category.id_comp, Category.comp_id] }
    have hnat := ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ
    have hnat' : h₁.extClass.comp (mk₀ (𝟙 _)) (add_zero 1) =
        (mk₀ (𝟙 _)).comp h₂.extClass (zero_add 1) := hnat
    have e3 : h₁.extClass = h₂.extClass :=
      (comp_mk₀_id _).symm.trans (hnat'.trans (mk₀_id_comp _))
    have e1 : ((hS.map_of_exact G₁).extClass).mapExactFunctor G₂ = h₁.extClass :=
      mapExactFunctor_extClass G₂ (hS.map_of_exact G₁)
    have e2 : hS.extClass.mapExactFunctor (G₁ ⋙ G₂) = h₂.extClass :=
      mapExactFunctor_extClass _ hS
    rw [mapExactFunctor_comp, mapExactFunctor_comp, mapExactFunctor_comp, ih,
      mapExactFunctor_extClass]
    exact congrArg (fun z ↦ (mapExactFunctor (G₁ ⋙ G₂) y).comp z _)
      (e1.trans (e3.trans e2.symm))

omit [HasExt.{w''} E] [EnoughInjectives C] [HasExt.{w} C] in
/-- Reassociation of a composite of `Ext`-classes along a commuting square. -/
lemma comp_comp_comp_aux {X Y Z W V V' : D} {n : ℕ} (i : Ext.{w'} X Y 0) (g : Ext Y Z n)
    (t₃ : Ext Z W 0) (e' : Ext W V 1) (e : Ext Z V' 1) (t : Ext V' V 0)
    (h : e.comp t (add_zero 1) = t₃.comp e' (zero_add 1)) :
    (i.comp (g.comp t₃ (add_zero n)) (zero_add n)).comp e' rfl =
      i.comp ((g.comp e rfl).comp t (add_zero _)) (zero_add _) := by
  rw [comp_assoc_of_third_deg_zero, h, ← comp_assoc_of_second_deg_zero]
  exact comp_assoc _ _ _ _ _ (by lia)

omit [HasExt.{w''} E] in
/-- Pushing an `Ext`-class forward along isomorphic exact functors gives conjugate classes. -/
lemma mapExactFunctor_eq_of_iso {G G' : C ⥤ D} [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [G'.Additive] [PreservesFiniteLimits G']
    [PreservesFiniteColimits G'] (τ : G ≅ G') {A B : C} {n : ℕ} (x : Ext.{w} A B n) :
    x.mapExactFunctor G' = (mk₀ (τ.inv.app A)).comp
      ((x.mapExactFunctor G).comp (mk₀ (τ.hom.app B)) (add_zero n)) (zero_add n) := by
  induction n generalizing B with
  | zero =>
    obtain ⟨f, rfl⟩ := (mk₀_bijective A B).2 x
    simp [mapExactFunctor_mk₀, mk₀_comp_mk₀]
  | succ n ih =>
    let ι := Injective.ι B
    let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι }
    obtain ⟨y, rfl⟩ := covariant_sequence_exact₁ A hS x (eq_zero_of_injective _) rfl
    have h₁ := hS.map_of_exact G
    have h₂ := hS.map_of_exact G'
    let φ : S.map G ⟶ S.map G' :=
      { τ₁ := τ.hom.app _, τ₂ := τ.hom.app _, τ₃ := τ.hom.app _
        comm₁₂ := (τ.hom.naturality S.f).symm, comm₂₃ := (τ.hom.naturality S.g).symm }
    have hnat : h₁.extClass.comp (mk₀ (τ.hom.app B)) (add_zero 1) =
        (mk₀ (τ.hom.app S.X₃)).comp h₂.extClass (zero_add 1) :=
      ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ
    have e1 : hS.extClass.mapExactFunctor G = h₁.extClass := mapExactFunctor_extClass _ hS
    have e2 : hS.extClass.mapExactFunctor G' = h₂.extClass := mapExactFunctor_extClass _ hS
    rw [mapExactFunctor_comp, mapExactFunctor_comp, ih, e1, e2]
    exact comp_comp_comp_aux _ _ _ _ _ _ hnat

set_option backward.isDefEq.respectTransparency false in
private lemma singleComparison_hom {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] (a : A) :
    (T.mapDerivedCategorySingleFunctor 0).hom.app a =
      T.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj a) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0).hom.app a) := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
    Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
  erw [Category.id_comp]

omit [EnoughInjectives C] in
/-- Let `G₁ : C ⥤ D`, `G₂ : D ⥤ E` and `G : C ⥤ E` be exact functors with an isomorphism
`τ : G ≅ G₁ ⋙ G₂`. Pushing a class of `Extⁿ(A, B)` forward along `G` agrees, up to `τ`, with
pushing it forward along `G₁` and then along `G₂`.

Source: Stacks Project, derived.tex, Tag 015F
(blueprint: lem-weil-pbc-ext-exact-functor-composition-comparison).

Proof: identify `Ext` with shifted morphisms between single complexes in the derived category.
The functor induced by `G` agrees with that induced by `G₁` followed by `G₂` through
`Functor.mapDerivedCategoryNatIso τ` and `Functor.mapDerivedCategoryCompIso G₁ G₂`, which
commute with the shifts. Naturality of this comparison for the shifted morphism representing
`x` gives the equality, once the comparisons with single complexes are cancelled. -/
lemma mapExactFunctor_comp_mk₀_eq (G₁ : C ⥤ D) [G₁.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (G : C ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : G ≅ G₁ ⋙ G₂) {A : C} (n : ℕ) :
    ∀ {B : C} (x : Ext A B n),
      (x.mapExactFunctor G).comp (mk₀ (τ.hom.app B)) (add_zero n) =
        (mk₀ (τ.hom.app A)).comp ((x.mapExactFunctor G₁).mapExactFunctor G₂) (zero_add n) := by
  intro B x
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard E
  set_option backward.isDefEq.respectTransparency false in
    let := comp_preservesFiniteLimits G₁ G₂
    let := comp_preservesFiniteColimits G₁ G₂
    have hc (A : C) :
        (Functor.mapDerivedCategoryNatIso τ ≪≫
            (Functor.mapDerivedCategoryCompIso G₁ G₂).symm).hom.app
            ((DerivedCategory.singleFunctor C 0).obj A) ≫
          G₂.mapDerivedCategory.map ((G₁.mapDerivedCategorySingleFunctor 0).hom.app A) ≫
          (G₂.mapDerivedCategorySingleFunctor 0).hom.app (G₁.obj A) =
        (G.mapDerivedCategorySingleFunctor 0).hom.app A ≫
          (DerivedCategory.singleFunctor E 0).map (τ.hom.app A) := by
      rw [singleComparison_hom G₁, singleComparison_hom G₂, singleComparison_hom G,
        Functor.map_comp]
      simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
      simp only [← DerivedCategory.Q_obj_single_obj] at *
      erw [G₂.mapDerivedCategoryFactors.hom.naturality_assoc]
      have hf := Functor.mapDerivedCategoryCompIso_fac G₁ G₂
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)
      have he := Functor.mapDerivedCategoryNatIso_fac τ
        ((HomologicalComplex.single C (.up ℤ) 0).obj A)
      simp only [Functor.comp_obj] at hf he
      have hm :
          (G₂.mapHomologicalComplex (.up ℤ)).map
              ((HomologicalComplex.singleMapHomologicalComplex G₁ (.up ℤ) 0).hom.app A) ≫
            (HomologicalComplex.singleMapHomologicalComplex G₂ (.up ℤ) 0).hom.app (G₁.obj A) =
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (.up ℤ)).hom.app
              ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
            (HomologicalComplex.singleMapHomologicalComplex (G₁ ⋙ G₂) (.up ℤ) 0).hom.app A := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
        · simp [HomologicalComplex.singleMapHomologicalComplex, hi]
      simp only [Functor.comp_map]
      rw [← DerivedCategory.Q.map_comp, hm, DerivedCategory.Q.map_comp]
      erw [reassoc_of% hf, reassoc_of% he]
      rw [← DerivedCategory.Q.map_comp]
      have hn :
          (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app
              ((HomologicalComplex.single C (.up ℤ) 0).obj A) ≫
            (HomologicalComplex.singleMapHomologicalComplex (G₁ ⋙ G₂) (.up ℤ) 0).hom.app A =
          (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app A ≫
            (HomologicalComplex.single E (.up ℤ) 0).map (τ.hom.app A) := by
        ext i
        by_cases hi : i = 0
        · subst i
          simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.single]
        · simp [HomologicalComplex.singleMapHomologicalComplex, hi]
      rw [hn, DerivedCategory.Q.map_comp]
      rfl
    ext
    simp only [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom]
    have : NatTrans.CommShift
        (Functor.mapDerivedCategoryNatIso τ ≪≫
          (Functor.mapDerivedCategoryCompIso G₁ G₂).symm).hom ℤ := by
      dsimp only [Iso.trans_hom]
      infer_instance
    have hi (A : C) :
        (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫
          (Functor.mapDerivedCategoryNatIso τ ≪≫
              (Functor.mapDerivedCategoryCompIso G₁ G₂).symm).hom.app
            ((DerivedCategory.singleFunctor C 0).obj A) =
        (DerivedCategory.singleFunctor E 0).map (τ.hom.app A) ≫
          (G₂.mapDerivedCategorySingleFunctor 0).inv.app (G₁.obj A) ≫
          G₂.mapDerivedCategory.map ((G₁.mapDerivedCategorySingleFunctor 0).inv.app A) := by
      rw [← cancel_mono (G₂.mapDerivedCategory.map
        ((G₁.mapDerivedCategorySingleFunctor 0).hom.app A) ≫
        (G₂.mapDerivedCategorySingleFunctor 0).hom.app (G₁.obj A))]
      simp only [Category.assoc]
      rw [hc A, Iso.inv_hom_id_app_assoc,
        ← G₂.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
      erw [G₂.mapDerivedCategory.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    have h := ShiftedHom.map_naturality x.hom
      (Functor.mapDerivedCategoryNatIso τ ≪≫ (Functor.mapDerivedCategoryCompIso G₁ G₂).symm).hom
    simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
      ShiftedHom.map, Functor.map_comp, Category.assoc] at h ⊢
    have hh := congrArg (fun t ↦ (G.mapDerivedCategorySingleFunctor 0).inv.app A ≫ t ≫
        (G₂.mapDerivedCategory.map ((G₁.mapDerivedCategorySingleFunctor 0).hom.app B) ≫
          (G₂.mapDerivedCategorySingleFunctor 0).hom.app (G₁.obj B))⟦(n : ℤ)⟧') h
    simp only [Category.assoc, ← Functor.map_comp, hc] at hh
    rw [reassoc_of% (hi A)] at hh
    simp only [Functor.map_comp, Functor.comp_map, Functor.commShiftIso_comp_hom_app,
      Category.assoc] at hh
    simp only [← Functor.commShiftIso_hom_naturality_assoc] at hh
    exact hh

omit [EnoughInjectives C] in
/-- Let `G₁ : C ⥤ D`, `G₂ : D ⥤ E` and `G : C ⥤ E` be exact functors with `G ≅ G₁ ⋙ G₂`, and
let `x` be a class of `Extⁿ(A, B)`. Pushing `x` forward along `G₁`, pulling it back along an
isomorphism `u₁ : A₁ ⟶ G₁ A`, pushing forward along `G₂` and pulling back along an isomorphism
`u₂ : A₂ ⟶ G₂ A₁` gives zero exactly when pushing `x` forward along `G` and pulling it back
along an isomorphism `u : A₂ ⟶ G A` gives zero. -/
lemma mk₀_comp_mapExactFunctor_comp_eq_zero_iff' (G₁ : C ⥤ D) [G₁.Additive]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁] (G₂ : D ⥤ E) [G₂.Additive]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂] (G : C ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (τ : G ≅ G₁ ⋙ G₂) {A B : C}
    {A₁ : D} {A₂ : E} (u₁ : A₁ ⟶ G₁.obj A) (u₂ : A₂ ⟶ G₂.obj A₁) (u : A₂ ⟶ G.obj A)
    [IsIso u₁] [IsIso u₂] [IsIso u] {n : ℕ} (x : Ext A B n) :
    (mk₀ u₂).comp (((mk₀ u₁).comp (x.mapExactFunctor G₁) (zero_add n)).mapExactFunctor G₂)
        (zero_add n) = 0 ↔
      (mk₀ u).comp (x.mapExactFunctor G) (zero_add n) = 0 := by
  have h := mapExactFunctor_comp_mk₀_eq G₁ G₂ G τ n x
  have h' : (x.mapExactFunctor G₁).mapExactFunctor G₂ =
      (mk₀ (τ.inv.app A)).comp ((x.mapExactFunctor G).comp (mk₀ (τ.hom.app B)) (add_zero n))
        (zero_add n) := by
    rw [h, ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, Iso.inv_hom_id_app, mk₀_id_comp]
  rw [mapExactFunctor_comp, mapExactFunctor_mk₀, ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
    h', ← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, mk₀_comp_eq_zero_iff_of_isIso,
    comp_mk₀_eq_zero_iff_of_isIso, mk₀_comp_eq_zero_iff_of_isIso]


end CategoryTheory.Abelian.Ext
