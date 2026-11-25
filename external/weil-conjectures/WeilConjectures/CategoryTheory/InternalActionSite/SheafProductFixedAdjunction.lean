/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionInflation
public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Normalized fixed-subsheaf adjunctions for a product of group sheaves

Source: main-20261015, direct-image stability paragraph (3), agent-formulated
fixed-subsheaf input; Stacks Tags 03CV, 00VH, 00VM, 0037, 0DV0
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).

The action categories and their sectionwise additive structures are the existing
`InternalActionSite.EquivariantSheaf` categories, recorded by the definition node
`def-sfb-equivariant-module-sheaves`. The specifications below identify
invariants by their injective inclusions and exact fixed-section images. No invariant
object or comparison is chosen from an unspecified existence assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

/-- The pair-valued group restriction maps obey the functor laws.
Source: product of group sheaves in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction).
Proof: evaluate each equation on a pair. In each coordinate the identity equation
is the corresponding group presheaf's map-identity law, and the composition equation
is its map-composition law. Extensionality of group homomorphisms concludes. -/
theorem productGroup_laws (K L : Cᵒᵖ ⥤ GrpCat.{u}) :
    (∀ X : Cᵒᵖ, GrpCat.ofHom ((K.map (𝟙 X)).hom.prodMap (L.map (𝟙 X)).hom) =
      𝟙 (GrpCat.of (K.obj X × L.obj X))) ∧
    (∀ (X Y Z : Cᵒᵖ) (f : X ⟶ Y) (g : Y ⟶ Z),
      GrpCat.ofHom ((K.map (f ≫ g)).hom.prodMap (L.map (f ≫ g)).hom) =
        GrpCat.ofHom ((K.map f).hom.prodMap (L.map f).hom) ≫
          GrpCat.ofHom ((K.map g).hom.prodMap (L.map g).hom)) := by
  constructor
  · intro X
    simp only [Functor.map_id]
    rfl
  · intro X Y Z f g
    simp only [Functor.map_comp]
    rfl

/-- Sectionwise product, retaining actual pairs of group sections.
Source: product-action calculation in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
def productGroup (K L : Cᵒᵖ ⥤ GrpCat.{u}) : Cᵒᵖ ⥤ GrpCat.{u} where
  obj X := GrpCat.of (K.obj X × L.obj X)
  map f := GrpCat.ofHom ((K.map f).hom.prodMap (L.map f).hom)
  map_id := (productGroup_laws K L).1
  map_comp := (productGroup_laws K L).2 _ _ _

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Fixedness is tested after every base change, including the identity restriction.
Source: invariant-section formula in paragraph (3)
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
def FixedSection {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) (m : M.obj.val.obj X) : Prop :=
  ∀ (Y : Cᵒᵖ) (f : X ⟶ Y) (p : P.obj Y),
    M.obj.action.act Y p (M.obj.val.map f m) = M.obj.val.map f m

/-- A fixed-subsheaf functor with its normalized additive adjunction. Injectivity and
image specify the displayed subsheaf; the transpose equations retain every section map.
Source: fixed-subsheaf construction and Stacks 0037
(blueprint: lem-sfb-sheaf-product-fixed-adjunction). -/
structure SheafFixedAdjunction (P : Cᵒᵖ ⥤ GrpCat.{u}) where
  /-- Restriction of equivariant maps to invariant sections. -/
  functor : EquivariantSheaf (K := P) J R ⥤ ringedSiteModules.{u} R
  /-- Sectionwise addition is preserved. -/
  additive : functor.Additive
  /-- The natural invariant inclusion. -/
  inclusion : functor ⟶ forgetSheaf (K := P) J R
  /-- Trivial action is additive. -/
  trivial_additive : (trivialSheafAction R P).Additive
  /-- The adjunction with trivial action. -/
  adjunction : trivialSheafAction R P ⊣ functor
  /-- Each component inclusion is injective on sections. -/
  injective (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) :
    Function.Injective ((inclusion.app M).val.app X)
  /-- Its sectionwise image is exactly the displayed invariant subset. -/
  image (M : EquivariantSheaf (K := P) J R) (X : Cᵒᵖ) (m : M.obj.val.obj X) :
    (∃ x : (functor.obj M).val.obj X, (inclusion.app M).val.app X x = m) ↔
      FixedSection R M X m
  /-- Forward transposition restricts the codomain and keeps the map. -/
  transpose (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f : (trivialSheafAction R P).obj A ⟶ M) :
    adjunction.homEquiv A M f ≫ inclusion.app M = ⟨f.hom.val⟩
  /-- Inverse transposition composes with the invariant inclusion. -/
  untranspose (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f : A ⟶ functor.obj M) :
    ((adjunction.homEquiv A M).symm f).hom.val = (f ≫ inclusion.app M).val
  /-- The normalized Hom bijection preserves sums. -/
  transpose_add (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R)
      (f g : (trivialSheafAction R P).obj A ⟶ M) :
    adjunction.homEquiv A M (f + g) =
      adjunction.homEquiv A M f + adjunction.homEquiv A M g

private def fixedSubmodule {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) : M.obj.val.Submodule where
  obj X :=
    { carrier := {m | FixedSection R M X m}
      zero_mem' := by intro Y f p; simp
      add_mem' := by
        intro m n hm hn Y f p
        simp only [map_add, hm Y f p, hn Y f p]
      smul_mem' := by
        intro a m hm Y f p
        rw [M.obj.val.map_smul, map_smul, hm Y f p] }
  map {X Y} f := by
    intro m hm Z g p
    simpa only [PresheafOfModules.restrictₛₗ_apply,
      ← PresheafOfModules.map_comp_apply] using hm Z (f ≫ g) p

private def fixedSubfunctor {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) :
    Subfunctor (M.obj.val.presheaf ⋙ forget AddCommGrpCat.{u}) where
  obj X := {m | FixedSection R M X m}
  map f := (fixedSubmodule R M).map f

private theorem fixed_isSheaf {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) :
    Presheaf.IsSheaf J (fixedSubmodule R M).toPresheafOfModules.presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have hM : Presieve.IsSheaf J (M.obj.val.presheaf ⋙ forget AddCommGrpCat.{u}) := by
    rw [← isSheaf_iff_isSheaf_of_type,
      ← Presheaf.isSheaf_iff_isSheaf_forget (s := forget AddCommGrpCat.{u})]
    exact M.property
  change Presieve.IsSheaf J (fixedSubfunctor R M).toFunctor
  -- Membership in the fixed submodule is local; separatedness detects the action equation.
  apply (Subfunctor.isSheaf_iff _ hM).2
  intro X m hm Y f p
  apply (hM _ (J.pullback_stable f.unop hm)).isSeparatedFor.ext
  intro Z g hg
  change M.obj.val.map g.op (M.obj.action.act Y p (M.obj.val.map f m)) =
    M.obj.val.map g.op (M.obj.val.map f m)
  rw [M.obj.action.naturality]
  have hfix : FixedSection R M (op Z) (M.obj.val.map (g ≫ f.unop).op m) := hg
  have he := hfix (op Z) (𝟙 _) (P.map g.op p)
  simpa [PresheafOfModules.map_comp_apply] using he

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedSheaf {P : Cᵒᵖ ⥤ GrpCat.{u}}
    (M : EquivariantSheaf (K := P) J R) : ringedSiteModules.{u} R :=
  ⟨(fixedSubmodule R M).toPresheafOfModules, fixed_isSheaf R M⟩

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedMap {P : Cᵒᵖ ⥤ GrpCat.{u}}
    {M N : EquivariantSheaf (K := P) J R} (a : M ⟶ N) :
    fixedSheaf R M ⟶ fixedSheaf R N where
  val :=
    { app X := ModuleCat.ofHom
        { toFun := fun x ↦ ⟨a.hom.val.app X x.val, by
            intro Y f p
            rw [← PresheafOfModules.naturality_apply]
            rw [← a.hom.property, x.property Y f p]⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      naturality := by
        intro X Y f
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply a.hom.val f x.val }

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedFunctor (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    EquivariantSheaf (K := P) J R ⥤ ringedSiteModules.{u} R where
  obj M := fixedSheaf R M
  map a := fixedMap R a
  map_id M := by ext X x; rfl
  map_comp a b := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedInclusion (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    fixedFunctor R P ⟶ forgetSheaf (K := P) J R where
  app M := ⟨(fixedSubmodule R M).ι⟩
  naturality {M N} a := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedHomEquiv (P : Cᵒᵖ ⥤ GrpCat.{u})
    (A : ringedSiteModules.{u} R) (M : EquivariantSheaf (K := P) J R) :
    ((trivialSheafAction R P).obj A ⟶ M) ≃ (A ⟶ (fixedFunctor R P).obj M) where
  toFun a :=
    ⟨{ app X := ModuleCat.ofHom
        { toFun := fun x ↦ ⟨a.hom.val.app X x, by
            intro Y f p
            rw [← PresheafOfModules.naturality_apply]
            exact (a.hom.property Y p (A.val.map f x)).symm⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
       naturality := by
         intro X Y f
         ext x
         apply Subtype.ext
         exact PresheafOfModules.naturality_apply a.hom.val f x }⟩
  invFun a := ObjectProperty.homMk
    ⟨a.val ≫ (fixedSubmodule R M).ι, by
      intro X p x
      have h := (a.val.app X x).property X (𝟙 X) p
      change (a.val.app X x).val = M.obj.action.act X p (a.val.app X x).val
      simpa using h.symm⟩
  left_inv a := by
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    ext X x
    rfl
  right_inv a := by ext X x; rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def fixedAdjunction (P : Cᵒᵖ ⥤ GrpCat.{u}) :
    SheafFixedAdjunction R P where
  functor := fixedFunctor R P
  additive := { map_add := by intros; ext X x; rfl }
  inclusion := fixedInclusion R P
  trivial_additive :=
    { map_add := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        rfl }
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := fixedHomEquiv R P
      homEquiv_naturality_left_symm := by
        intros
        apply ObjectProperty.hom_ext
        apply Subtype.ext
        ext X x
        rfl
      homEquiv_naturality_right := by intros; ext X x; rfl }
  injective M X := Subtype.val_injective
  image M X m := ⟨fun ⟨x,h⟩ ↦ h ▸ x.property, fun h ↦ ⟨⟨m,h⟩,rfl⟩⟩
  transpose A M a := by ext X x; rfl
  untranspose A M a := rfl
  transpose_add A M a b := by ext X x; rfl

end CategoryTheory.InternalActionSite
