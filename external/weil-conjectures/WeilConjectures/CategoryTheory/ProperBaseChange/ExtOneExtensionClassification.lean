/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Degree-one Ext classes classify short exact extensions

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV; exact-functor compatibility
by Tags 0151 and 0152 (blueprint: lem-weil-pbc-ext-one-extension-classification).
-/

@[expose] public section

universe w w' t t' v v' u u'

open CategoryTheory.Limits

namespace CategoryTheory

open Category _root_.DerivedCategory Pretriangulated

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem single_shift_negative_zero
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
    {X Y : C} {n : ℤ}
    (f : (singleFunctor C 0).obj X ⟶ ((singleFunctor C 0).obj Y)⟦n⟧)
    (hn : n < 0) : f = 0 := by
  have := TStructure.t.isGE_shift ((singleFunctor C 0).obj Y) 0 n (-n) (by lia)
  exact TStructure.t.zero f 0 (-n) (by lia)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem shortExact_of_single_triangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
    (S : ShortComplex C)
    (δ : (singleFunctor C 0).obj S.X₃ ⟶ ((singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map S.f) ((singleFunctor C 0).map S.g) δ ∈
      distTriang (DerivedCategory C)) : S.ShortExact := by
  have hf := Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
    (ι := singleFunctor C 0) (fun {_ _ _} f hn ↦ single_shift_negative_zero f hn) S.f S.g δ hT
  have hg := Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
    (ι := singleFunctor C 0) (fun {_ _ _} f hn ↦ single_shift_negative_zero f hn) S.f S.g δ hT
  have : Mono S.f := mono_of_isLimit_fork hf
  have : Epi S.g := epi_of_isColimit_cofork hg
  exact ⟨S.exact_of_f_is_kernel hf⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem single_triangle_boundary_unique
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{t} C]
    {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (δ δ' : (singleFunctor C 0).obj Z ⟶ ((singleFunctor C 0).obj X)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) δ ∈
      distTriang (DerivedCategory C))
    (hT' : Triangle.mk ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) δ' ∈
      distTriang (DerivedCategory C)) : δ = δ' := by
  obtain ⟨(c : (singleFunctor C 0).obj Z ⟶ (singleFunctor C 0).obj Z), hc₁, hc₂⟩ :=
    complete_distinguished_triangle_morphism _ _ hT hT' (𝟙 _) (𝟙 _) (by simp)
  have hc₁' : (singleFunctor C 0).map b ≫ c = (singleFunctor C 0).map b := by
    simpa using hc₁
  have hc₂' : δ = c ≫ δ' := by simpa using hc₂
  have hc : c = 𝟙 _ := by
    rw [← sub_eq_zero]
    obtain ⟨w, hw⟩ := Triangle.yoneda_exact₃ _ hT (c - 𝟙 _) (by
      change (singleFunctor C 0).map b ≫ (c - 𝟙 _) = 0
      rw [Preadditive.comp_sub, hc₁', comp_id, sub_self])
    have hle : TStructure.t.IsLE (((singleFunctor C 0).obj X)⟦(1 : ℤ)⟧) (-1) :=
      TStructure.t.isLE_shift _ 0 1 (-1) (by lia)
    rw [hw, TStructure.t.zero_of_isLE_of_isGE w (-1) 0 (by lia) hle
      (inferInstanceAs (TStructure.t.IsGE ((singleFunctor C 0).obj Z) 0)), comp_zero]
  rw [hc₂', hc, id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Short exact extensions with fixed endpoints are classified by their connecting class.
Source: Stacks Project, Tags 06XU and 06XV
(blueprint: lem-weil-pbc-ext-one-extension-classification).

The first clause gives every class a representative. The second says precisely that equal
classes have an isomorphism of middle objects inducing identities on both endpoints; its
reverse implication also makes the class assignment well-defined on isomorphism classes.
The third clause is compatibility with every exact additive functor. Under `Ext.homAddEquiv`,
`h.extClass` is the connecting map `h.singleδ` by `ShortExact.extClass_hom`, and
`Ext.mapExactFunctor_hom` identifies `mapExactFunctor` with the termwise derived functor,
including its single-complex and shift comparisons.

Proof plan: identify the standard heart with the original abelian category using concentration
in degree zero and full faithfulness of the single functor. Transfer short exactness across
this equivalence. The single-complex short exact sequence triangle supplies the boundary;
its naturality makes endpoint-identity isomorphisms preserve the class. Complete an arbitrary
degree-one arrow to a triangle and inverse-rotate twice. Extension closure of the standard
heart puts the middle object in the heart, so it is a single object, and the heart criterion
makes the lifted sequence short exact with the prescribed boundary. For injectivity, rotate
two triangles with equal boundaries twice and apply TR3 with identities on the common first
two objects. The third component is an isomorphism by the two-isomorphisms criterion; shift
back and lift it through the fully faithful single functor to the required middle-object
isomorphism. Finally apply the exact-functor short-exact-triangle comparison; uniqueness of
the heart boundary identifies it with the canonical boundary of the image sequence.
-/
theorem ext_one_extension_classification
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{w} C] (P Q : C) :
    (∀ ξ : Abelian.Ext Q P 1,
      ∃ (B : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
        (h : (ShortComplex.mk a b z).ShortExact), h.extClass = ξ) ∧
    (∀ (B B' : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
      (h : (ShortComplex.mk a b z).ShortExact)
      (a' : P ⟶ B') (b' : B' ⟶ Q) (z' : a' ≫ b' = 0)
      (h' : (ShortComplex.mk a' b' z').ShortExact),
      h.extClass = h'.extClass ↔ ∃ e : B ≅ B', a ≫ e.hom = a' ∧ e.hom ≫ b' = b) ∧
    (∀ (D : Type u') [Category.{v'} D] [Abelian D]
      [HasDerivedCategory.{t'} D] [HasExt.{w'} D]
      (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (B : C) (a : P ⟶ B) (b : B ⟶ Q) (z : a ≫ b = 0)
      (h : (ShortComplex.mk a b z).ShortExact),
      h.extClass.mapExactFunctor F = (h.map_of_exact F).extClass) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro ξ
    obtain ⟨M, f, g, hT⟩ := distinguished_cocone_triangle₂ ξ.hom
    have hle : M.IsLE 0 := TStructure.t.isLE₂ _ hT 0
      (by change ((singleFunctor C 0).obj P).IsLE 0; infer_instance)
      (by change ((singleFunctor C 0).obj Q).IsLE 0; infer_instance)
    have hge : M.IsGE 0 := TStructure.t.isGE₂ _ hT 0
      (by change ((singleFunctor C 0).obj P).IsGE 0; infer_instance)
      (by change ((singleFunctor C 0).obj Q).IsGE 0; infer_instance)
    obtain ⟨B, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M 0
    let a : P ⟶ B := (singleFunctor C 0).preimage (f ≫ e.hom)
    let b : B ⟶ Q := (singleFunctor C 0).preimage (e.inv ≫ g)
    have ha : (singleFunctor C 0).map a = f ≫ e.hom := Functor.map_preimage _ _
    have hb : (singleFunctor C 0).map b = e.inv ≫ g := Functor.map_preimage _ _
    have hz : a ≫ b = 0 := (singleFunctor C 0).map_injective (by
      rw [Functor.map_comp, Functor.map_zero, ha, hb]
      simpa using comp_distTriang_mor_zero₁₂ _ hT)
    have hT' : Triangle.mk ((singleFunctor C 0).map a) ((singleFunctor C 0).map b)
        ξ.hom ∈ distTriang (DerivedCategory C) := by
      refine isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_)
      · simp [ha]
      · simp [hb]
      · simp
    have h := shortExact_of_single_triangle (ShortComplex.mk a b hz) ξ.hom hT'
    refine ⟨B, a, b, hz, h, ?_⟩
    apply Abelian.Ext.ext
    rw [ShortComplex.ShortExact.extClass_hom]
    exact single_triangle_boundary_unique a b _ _ h.singleTriangle_distinguished hT'
  · intro B B' a b z h a' b' z' h'
    constructor
    · intro heq
      have hd : ShortComplex.ShortExact.singleδ.{t} h =
          ShortComplex.ShortExact.singleδ.{t} h' := by
        rw [← ShortComplex.ShortExact.extClass_hom.{t, w} h,
          ← ShortComplex.ShortExact.extClass_hom.{t, w} h']
        exact congrArg (fun x : Abelian.Ext Q P 1 ↦ Abelian.Ext.hom.{t, w} x) heq
      obtain ⟨m, hm₁, hm₂⟩ := complete_distinguished_triangle_morphism₂
        _ _ h.singleTriangle_distinguished h'.singleTriangle_distinguished
        (𝟙 _) (𝟙 _) (by simp [hd])
      let φ : h.singleTriangle ⟶ h'.singleTriangle :=
        Triangle.homMk _ _ (𝟙 _) m (𝟙 _) hm₁ hm₂ (by simp [hd])
      have hm : IsIso m := isIso₂_of_isIso₁₃ φ h.singleTriangle_distinguished
        h'.singleTriangle_distinguished (by change IsIso (𝟙 _); infer_instance)
        (by change IsIso (𝟙 _); infer_instance)
      let e : B ≅ B' := (singleFunctor C 0).preimageIso (asIso m)
      refine ⟨e, (singleFunctor C 0).map_injective ?_,
        (singleFunctor C 0).map_injective ?_⟩
      · simpa [e] using hm₁
      · simpa [e] using hm₂.symm
    · rintro ⟨e, ha, hb⟩
      let φ : ShortComplex.mk a b z ⟶ ShortComplex.mk a' b' z' :=
        { τ₁ := 𝟙 P
          τ₂ := e.hom
          τ₃ := 𝟙 Q
          comm₁₂ := by simpa using ha.symm
          comm₂₃ := by simpa using hb }
      have hn := h.extClass_naturality h' φ
      simpa [φ] using hn
  · intro D _ _ _ _ F _ _ _ B a b z h
    exact Abelian.Ext.mapExactFunctor_extClass F h

end CategoryTheory
