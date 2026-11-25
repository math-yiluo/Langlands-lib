/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorSummandRestriction
import WeilConjectures.Algebra.Homology.HomTensorSummandLocalizedExt

/-!
# Localized pure-tensor extensionality

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-localized-ext)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

-- The source tensor-Hom API uses one universe for the site and the coefficients.
-- These private constructions repeat its elementary proof with independent site universes.
-- Source: WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom, TensorHom.
namespace LocalTensorHom

open PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}

variable (M) in
/-- The morphism `M(X) ⟶ (M ⊗ P)(X)` sending `m` to `m ⊗ p`, for a section `p` of `P` over
`X`. -/
private noncomputable def tmulRight {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

@[local simp]
private lemma tmulRight_apply
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   {X : Cᵒᵖ} (p : P.obj X) (m : M.obj X) :
    tmulRight M p m = m ⊗ₜ[R.obj X] p :=
  rfl

/-- Auxiliary definition for `homObjEquiv`: a morphism `φ : M ⊗ P ⟶ N` and a section `p` of `P`
over `U` give the morphism `M|_U ⟶ N|_U` sending a section `m` of `M` over `W ⟶ U` to
`φ (m ⊗ p|_W)`. -/
private noncomputable def tensorHomCurryApp (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
  naturality {W W'} f := by
    ext m
    refine (congrArg (φ.app (op W'.unop.left)) ?_).trans
      (naturality_apply φ f.unop.left.op (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p))
    refine (congrArg (fun q : P.obj (op W'.unop.left) ↦
      TensorProduct.tmul (R.obj (op W'.unop.left))
        (M := M.obj (op W'.unop.left)) (N := P.obj (op W'.unop.left))
        (M.map f.unop.left.op m) q) ?_).trans
        (Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    rw [← map_comp_apply, ← op_comp, Over.w]

@[local simp]
private lemma tensorHomCurryApp_app_apply
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp φ (p + p') = tensorHomCurryApp φ p + tensorHomCurryApp φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, tensorHomCurryApp_app_apply, map_add, TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp φ (r • p) = r • tensorHomCurryApp φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp (U := V) φ (P.map g.op p) = restrictOverMap g (tensorHomCurryApp φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply, ← map_comp_apply]
  rfl

/-- Auxiliary definition for `homObjEquiv`: the morphism `P ⟶ homObj M N` corresponding to a
morphism `φ : M ⊗ P ⟶ N`. -/
private noncomputable def tensorHomCurry (φ : M ⊗ P ⟶ N) : P ⟶ homObj M N where
  app X := ModuleCat.ofHom (X := P.obj X) (Y := (homObj M N).obj X)
    { toFun p := tensorHomCurryApp φ p
      map_add' := tensorHomCurryApp_add φ
      map_smul' := tensorHomCurryApp_smul φ }
  naturality {X Y} g := by
    ext p : 2
    exact tensorHomCurryApp_map φ g.unop p

@[local simp]
private lemma tensorHomCurry_app_apply
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (p : P.obj X) :
    (tensorHomCurry φ).app X p = tensorHomCurryApp φ p :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
/-- Evaluation of a section of `homObj M N` over `U` at `Over.mk (𝟙 U)`, as a linear map. -/
private noncomputable def homObjEvalId (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

@[local simp]
private lemma homObjEvalId_apply_apply
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (U : C) (φ : (homObj M N).obj (op U)) (m : M.obj (op U)) :
    homObjEvalId M N U φ m = φ.app (op (Over.mk (𝟙 U))) m :=
  rfl

/-- Auxiliary definition for `homObjEquiv`: the morphism `M ⊗ P ⟶ N` corresponding to a
morphism `ψ : P ⟶ homObj M N`, sending `m ⊗ p` to `ψ p` evaluated at `m`. -/
private noncomputable def tensorHomUncurry (ψ : P ⟶ homObj M N) : M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((homObjEvalId M N X.unop).comp (ψ.app X).hom).flip)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N ↦
      ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) (naturality_apply ψ f p)).trans ?_
    refine (restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (ψ.app X p) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

@[local simp]
private lemma tensorHomUncurry_app_tmul
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ CommRingCat RingCat)}
   (ψ : P ⟶ homObj M N) (X : Cᵒᵖ) (m : M.obj X) (p : P.obj X) :
    (tensorHomUncurry ψ).app X (m ⊗ₜ[R.obj X] p) =
      (ψ.app X p).app (op (Over.mk (𝟙 X.unop))) m :=
  rfl

/-- The tensor-hom adjunction for presheaves of modules: morphisms `M ⊗ P ⟶ N` correspond to
morphisms `P ⟶ homObj M N`. A morphism `φ : M ⊗ P ⟶ N` is sent to the morphism which sends a
section `p` of `P` over `U` to `m ↦ φ (m ⊗ p|_W)` for `W ⟶ U` and `m` a section of `M` over
`W`. -/
private noncomputable def homObjEquiv (M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N) where
  toFun := tensorHomCurry
  invFun := tensorHomUncurry
  left_inv φ := by
    ext X : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine congrArg (fun q : P.obj X ↦ φ.app X (m ⊗ₜ[R.obj X] q)) (?_ : P.map (𝟙 X) p = p)
    rw [map_id]
    rfl
  right_inv ψ := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
    refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
      fun W ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
    refine (congrArg (fun ξ : (restrictOver R W.unop.left).obj M ⟶
        (restrictOver R W.unop.left).obj N ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) m)
      (naturality_apply ψ W.unop.hom.op p)).trans ?_
    exact restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp W.unop.hom) m

end LocalTensorHom


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

-- Transposing the internal Hom unfolds the localized module structures in two universes.
set_option synthInstance.maxSize 256 in
/-- Maps to the internal Hom out of a total tensor are determined on localized pure tensors.
Source: Stacks Project, Cohomology on Sites, Tag 0A90, degreewise construction;
Modules on Sites, Section 03EK, tensor product universal property.
(blueprint: lem-sc-hom-tensor-localized-ext)

Proof: Fix a source section over U and regard its images as morphisms on the
localized site over U. Restrict each such morphism to every total tensor summand.
The tensor summand is the sheafification of the presheaf tensor. Equality on
pure tensors gives equality on the presheaf tensor by its bilinear universal
property. The sheafification adjunction gives equality on the sheaf tensor,
including after localization, since sheafification commutes with restriction
to a localized site. The coproduct universal property gives equality on the
total term. Finally extensionality of internal-Hom sections, linear maps and
sheaf morphisms gives equality of the two original morphisms. -/
theorem homTensorLocalized_ext
    (K L : CochainComplex Mod ℤ) (N X : Mod) (p : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∀ (a b : X ⟶ SheafOfModules.homObj (R := R)
      ((CochainComplex.mapBifunctor K L (curriedTensor Mod)).X p) N),
    (∀ (U : Cᵒᵖ) (s : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
      (i j : ℤ) (hij : i + j = p)
      (x : (K.X i).val.obj (op W.unop.left))
      (y : (L.X j).val.obj (op W.unop.left)),
      (((a.val.app U).hom s).app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j p hij).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (((b.val.app U).hom s).app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j p hij).val.app (op W.unop.left)).hom
          (((homTensorSectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))) → a = b := by
  let := SheafOfModules.monoidalCategory R
  intro a b h
  apply homTensorSummandRestriction_ext R K L p X N a b
  intro i j hij
  apply homTensorSummandLocalized_ext R (K.X i) (L.X j) N X
  intro U s W x y
  exact h U s W i j hij x y

end CategoryTheory
