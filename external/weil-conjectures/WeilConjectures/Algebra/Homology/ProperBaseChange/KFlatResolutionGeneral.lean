/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Category.Grp.AB

/-! # K-flat resolutions without identifying the site universes

Source: Stacks Project, Cohomology on Sites, Tag 06YS
(blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits Opposite
open scoped ZeroObject

namespace PresheafOfModules

open Opposite

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}

variable (M) in
private noncomputable def tmulRight_kfg {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

private noncomputable def tensorHomCurryApp_kfg (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight_kfg M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
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
private lemma tensorHomCurryApp_app_apply_kfg (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp_kfg φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add_kfg (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp_kfg φ (p + p') =
      tensorHomCurryApp_kfg φ p + tensorHomCurryApp_kfg φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply_kfg,
    tensorHomCurryApp_app_apply_kfg, tensorHomCurryApp_app_apply_kfg, map_add,
    TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul_kfg (φ : M ⊗ P ⟶ N) {U : C}
    (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp_kfg φ (r • p) = r • tensorHomCurryApp_kfg φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply_kfg,
    tensorHomCurryApp_app_apply_kfg, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map_kfg (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp_kfg (U := V) φ (P.map g.op p) =
      restrictOverMap g (tensorHomCurryApp_kfg φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply_kfg, ← map_comp_apply]
  rfl

private noncomputable def tensorHomCurry_kfg (φ : M ⊗ P ⟶ N) : P ⟶ homObj M N where
  app X := ModuleCat.ofHom (X := P.obj X) (Y := (homObj M N).obj X)
    { toFun p := tensorHomCurryApp_kfg φ p
      map_add' := tensorHomCurryApp_add_kfg φ
      map_smul' := tensorHomCurryApp_smul_kfg φ }
  naturality {X Y} g := by
    ext p : 2
    exact tensorHomCurryApp_map_kfg φ g.unop p

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
private noncomputable def homObjEvalId_kfg (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

private noncomputable def tensorHomUncurry_kfg (ψ : P ⟶ homObj M N) : M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((homObjEvalId_kfg M N X.unop).comp (ψ.app X).hom).flip)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N ↦
      ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) (naturality_apply ψ f p)).trans ?_
    refine (restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (ψ.app X p) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

private noncomputable def homObjEquiv_kfg (M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N) where
  toFun := tensorHomCurry_kfg
  invFun := tensorHomUncurry_kfg
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

private lemma homObjEquiv_whiskerLeft_comp_kfg
    {M P P' N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}
    (f : P ⟶ P') (φ : M ⊗ P' ⟶ N) :
    homObjEquiv_kfg M P N (M ◁ f ≫ φ) = f ≫ homObjEquiv_kfg M P' N φ := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
    fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun q : P'.obj (op W.unop.left) ↦
    φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] q)) (naturality_apply f W.unop.hom.op p)

private lemma homObjEquiv_comp_homObjMap_kfg
    {M P N N' : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}
    (φ : M ⊗ P ⟶ N) (g : N ⟶ N') :
    homObjEquiv_kfg M P N' (φ ≫ g) =
      homObjEquiv_kfg M P N φ ≫ homObjMap (𝟙 M) g := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M)
    (M₂ := (restrictOver R X.unop).obj N') fun W ↦ ?_
  rfl

end PresheafOfModules

namespace SheafOfModules

private lemma tensorComparison_naturality_right_kfg
    {P S : Type*} [Category* P] [Category* S] [MonoidalCategory P] [MonoidalCategory S]
    (F : P ⥤ S) [F.LaxMonoidal] {A T T' : S} {M N N' : P}
    (a : A ⟶ F.obj M) (b : T ⟶ F.obj N) (b' : T' ⟶ F.obj N')
    (f : T ⟶ T') (g : N ⟶ N') (h : f ≫ b' = b ≫ F.map g) :
    A ◁ f ≫ (a ⊗ₘ b') ≫ Functor.LaxMonoidal.μ F M N' =
      (a ⊗ₘ b) ≫ Functor.LaxMonoidal.μ F M N ≫ F.map (M ◁ g) := by
  rw [← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc, whiskerLeft_comp_tensorHom, tensorHom_comp_whiskerLeft, h]

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{max u v} (𝟙 (𝓡).obj)

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  {R : Sheaf J CommRingCat.{max u v}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] [HasWeakSheafify J AddCommGrpCat.{max u v}]

attribute [local instance] monoidalCategory symmetricCategory

private noncomputable def sheafificationCounitIso_kfg (A : SheafOfModules.{max u v} 𝓡) :
    (𝓢).obj A.val ≅ A :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (𝓡).obj)).counit).app A

private lemma tensorObjIsoSheafification_hom_eq_kfg (A T : SheafOfModules.{max u v} 𝓡) :
    (tensorObjIsoSheafification A T).hom =
      ((sheafificationCounitIso_kfg A).inv ⊗ₘ (sheafificationCounitIso_kfg T).inv) ≫
        Functor.LaxMonoidal.μ (𝓢) A.val T.val := rfl

/-- The tensor comparison is natural in the second factor. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom_kfg (A : SheafOfModules.{max u v} 𝓡)
    {T T' : SheafOfModules.{max u v} 𝓡} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫ (𝓢).map (A.val ◁ f.val) := by
  have h : f ≫ (sheafificationCounitIso_kfg T').inv =
      (sheafificationCounitIso_kfg T).inv ≫ (𝓢).map f.val :=
    (asIso (PresheafOfModules.sheafificationAdjunction.{max u v}
      (𝟙 (𝓡).obj)).counit).inv.naturality f
  rw [tensorObjIsoSheafification_hom_eq_kfg, tensorObjIsoSheafification_hom_eq_kfg,
    Category.assoc]
  exact tensorComparison_naturality_right_kfg (𝓢) (A := A) (T := T) (T' := T')
    (M := A.val) (N := T.val) (N' := T'.val)
    (sheafificationCounitIso_kfg A).inv (sheafificationCounitIso_kfg T).inv
    (sheafificationCounitIso_kfg T').inv f f.val h

/-- **The tensor-hom adjunction for sheaves of modules**: morphisms `A ⊗ T ⟶ N` correspond to
morphisms `T ⟶ homObj A N`. A morphism `A ⊗ T ⟶ N` is a morphism `a(A ⊗ T) ⟶ N` out of the
sheafification of the presheaf tensor product, i.e. a morphism of presheaves `A ⊗ T ⟶ N`, which
`PresheafOfModules.homObjEquiv` turns into a morphism `T ⟶ homObj A N`. -/
private noncomputable def tensorHomEquiv_kfg (A T N : SheafOfModules.{max u v} 𝓡) :
    (A ⊗ T ⟶ N) ≃ (T ⟶ homObj A N) where
  toFun φ := ⟨PresheafOfModules.homObjEquiv_kfg (R := R.obj) A.val T.val N.val
    ((PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (𝓡).obj)).homEquiv _ N
      ((tensorObjIsoSheafification A T).inv ≫ φ))⟩
  invFun ψ := (tensorObjIsoSheafification A T).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (𝓡).obj)).homEquiv _ N).symm
      ((PresheafOfModules.homObjEquiv_kfg (R := R.obj) A.val T.val N.val).symm ψ.val)
  left_inv φ := by simp
  right_inv ψ := by
    ext1
    dsimp only
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private lemma tensorHomEquiv_val_kfg (A T N : SheafOfModules.{max u v} 𝓡) (φ : A ⊗ T ⟶ N) :
    (tensorHomEquiv_kfg A T N φ).val =
      PresheafOfModules.homObjEquiv_kfg (R := R.obj) A.val T.val N.val
      ((PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (𝓡).obj)).homEquiv _ N
        ((tensorObjIsoSheafification A T).inv ≫ φ)) :=
  rfl

/-- The tensor-hom adjunction for sheaves of modules is natural in `T`. -/
private lemma tensorHomEquiv_whiskerLeft_comp_kfg (A : SheafOfModules.{max u v} 𝓡)
    {T T' N : SheafOfModules.{max u v} 𝓡}
    (f : T ⟶ T') (φ : A ⊗ T' ⟶ N) :
    tensorHomEquiv_kfg A T N (A ◁ f ≫ φ) = f ≫ tensorHomEquiv_kfg A T' N φ := by
  have h : (tensorObjIsoSheafification A T).inv ≫ A ◁ f =
      (𝓢).map (A.val ◁ f.val) ≫ (tensorObjIsoSheafification A T').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_tensorObjIsoSheafification_hom_kfg,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, tensorHomEquiv_val_kfg, tensorHomEquiv_val_kfg, ← Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.homObjEquiv_whiskerLeft_comp_kfg _ _

/-- The tensor-hom adjunction for sheaves of modules is natural in `N`. -/
private lemma tensorHomEquiv_comp_homObjMap_kfg (A : SheafOfModules.{max u v} 𝓡)
    {T N N' : SheafOfModules.{max u v} 𝓡}
    (φ : A ⊗ T ⟶ N) (g : N ⟶ N') :
    tensorHomEquiv_kfg A T N' (φ ≫ g) = tensorHomEquiv_kfg A T N φ ≫ homObjMap (𝟙 A) g := by
  ext1
  rw [comp_val, tensorHomEquiv_val_kfg, tensorHomEquiv_val_kfg, ← Category.assoc,
    Adjunction.homEquiv_naturality_right]
  exact PresheafOfModules.homObjEquiv_comp_homObjMap_kfg _ _

variable (R) in
/-- **The tensor-hom adjunction for sheaves of modules**: tensoring with `A` is left adjoint to
the internal hom `homObj A`. -/
private noncomputable def tensorHomAdjunction_kfg (A : SheafOfModules.{max u v} 𝓡) :
    tensorLeft A ⊣ (homFunctor R).obj (Opposite.op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv_kfg A
      homEquiv_naturality_left_symm f g := by
        rw [Equiv.symm_apply_eq]
        exact ((congrArg (f ≫ ·) (Equiv.apply_symm_apply (tensorHomEquiv_kfg A _ _) g).symm).trans
          (tensorHomEquiv_whiskerLeft_comp_kfg A f _).symm)
      homEquiv_naturality_right f g := tensorHomEquiv_comp_homObjMap_kfg A f g }

/-- **Sheaves of modules form a monoidal closed category**, with internal hom `homObj`:
tensoring with `A` is left adjoint to `homObj A` (`SheafOfModules.tensorHomAdjunction_kfg`). -/
@[instance_reducible]
private noncomputable def monoidalClosed_kfg : MonoidalClosed (SheafOfModules.{max u v} 𝓡) where
  closed A := { rightAdj := (homFunctor R).obj (Opposite.op A), adj := tensorHomAdjunction_kfg R A }

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{max u v} O

attribute [local instance] monoidalCategory symmetricCategory monoidalClosed_kfg

private theorem monoidalPreadditive_kfg : MonoidalPreadditive A := by
  have (M : A) : (tensorLeft M).Additive := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := inferInstance
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft M)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

private theorem isGrothendieckAbelian_kfg : IsGrothendieckAbelian.{max u v} A := by
  have : HasFilteredColimitsOfSize.{max u v, max u v} A :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{max u v, max u v} A :=
    ⟨fun K _ _ ↦ HasExactColimitsOfShape.domain_of_functor K (toSheaf O)⟩
  let a := PresheafOfModules.sheafification.{max u v} (𝟙 (O).obj)
  let Y : C → A := fun X ↦ a.obj
    ((PresheafOfModules.free.{max u v} (O).obj).obj (uliftYoneda.{u}.obj X))
  have hY : ObjectProperty.IsSeparating (.ofObj Y) := by
    intro M N f g hfg
    apply (SheafOfModules.forget.{max u v} O ⋙
      PresheafOfModules.restrictScalars (𝟙 (O).obj)).map_injective
    apply (PresheafOfModules.toPresheaf.{max u v} (O).obj).map_injective
    apply ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)).map_injective
    apply hom_ext_uliftYoneda.{u}
    intro X k
    let adj := (PresheafOfModules.freeAdjunction (O).obj).comp
      (PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (O).obj))
    have h := hfg _ (ObjectProperty.ofObj_apply Y X) ((adj.homEquiv _ _).symm k)
    apply (adj.homEquiv _ _).symm.injective
    simpa only [Functor.comp_map, ← Adjunction.homEquiv_naturality_right_symm] using h
  have : HasSeparator A := ⟨_, hY.isSeparator_coproduct⟩
  exact {}

private noncomputable def tensorSheafificationIso_kfg
    (F : PresheafOfModules.{max u v} (O).obj) :
    tensorRight ((PresheafOfModules.sheafification.{max u v} (𝟙 (O).obj)).obj F) ≅
      (SheafOfModules.forget.{max u v} O ⋙
        PresheafOfModules.restrictScalars (𝟙 (O).obj)) ⋙ tensorRight F ⋙
        PresheafOfModules.sheafification.{max u v} (𝟙 (O).obj) := by
  let a := PresheafOfModules.sheafification.{max u v} (𝟙 (O).obj)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (O).obj)).counit
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight a F)

private theorem hasFunctorialFlatResolution_kfg : Abelian.HasFunctorialFlatResolution A := by
  let a := PresheafOfModules.sheafification.{max u v} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{max u v} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{max u v} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{max u v} (O).obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free ((O).obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{max u v} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 (O).obj)).counit
  have hT (M : A) : ObjectProperty.flat (T.obj M) := by
    have hflat : PreservesFiniteLimits (tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro D
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have := hflat
    have : PreservesLimitsOfSize.{0, 0} V :=
      (PresheafOfModules.sheafificationAdjunction.{max u v}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_kfg R (G.obj (V.obj M))).symm
    have : PreservesFiniteLimits (tensorLeft (T.obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M)).symm
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2 inferInstance
  exact ⟨{ F := ObjectProperty.lift _ T hT
           π := π
           epi_π_app M := by
             have := hτ (V.obj M)
             dsimp [π]
             infer_instance }⟩

end SheafOfModules

namespace CochainComplex

private theorem flat_biprod_kfg
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [IsGrothendieckAbelian A]
    {M N : A} (hM : ObjectProperty.flat M) (hN : ObjectProperty.flat N) :
    ObjectProperty.flat (M ⊞ N) := by
  apply ObjectProperty.prop_of_iso _ (biprod.isoProd M N).symm
  exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair M N))
    (by rintro ⟨_ | _⟩ <;> assumption)

private theorem flat_epicification_kfg
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [IsGrothendieckAbelian A]
    (hcover : ∀ M : A, ∃ (P : A) (p : P ⟶ M), ObjectProperty.flat P ∧ Epi p)
    (E H : CochainComplex A ℤ) (f : E ⟶ H)
    (hflat : ∀ i : ℤ, ObjectProperty.flat (E.X i)) :
    ∃ (F : CochainComplex A ℤ) (g : F ⟶ H) (e : HomotopyEquiv E F),
      (∀ i : ℤ, ObjectProperty.flat (F.X i)) ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ e.hom ≫ g = f := by
  classical
  choose Q p hQ hp using hcover
  let P (i : ℤ) := Q (H.X i)
  let q (i : ℤ) : P i ⟶ H.X i := p (H.X i)
  have hP (i : ℤ) : ObjectProperty.flat (P i) := hQ _
  have hq (i : ℤ) : Epi (q i) := hp _
  let X (i : ℤ) := P i ⊞ P (i - 1)
  let dd (i j : ℤ) : X i ⟶ X j :=
    if hij : i + 1 = j then
      biprod.fst ≫ eqToHom (by congr 1; omega) ≫ biprod.inr
    else 0
  let D : CochainComplex _ ℤ :=
    { X := X
      d := dd
      shape := fun i j hij ↦ dite_eq_right hij
      d_comp_d' := by
        intro i j k hij hjk
        change i + 1 = j at hij
        change j + 1 = k at hjk
        simp [dd, hij, hjk, Category.assoc] }
  let a : D ⟶ H := CochainComplex.ofHom
    (fun i ↦ biprod.desc (q i) (q (i - 1) ≫ H.d (i - 1) i)) (by
      intro i
      have hi : i + 1 - 1 = i := by omega
      apply biprod.hom_ext'
      · simp only [D, dd, dite_eq_left rfl, Category.assoc,
          biprod.inl_fst_assoc, biprod.inr_desc]
        simpa using (eqToHom_naturality
          (fun k ↦ q k ≫ H.d k (i + 1)) hi.symm)
      · simp [D, dd, Category.assoc])
  have ha (i : ℤ) : Epi (a.f i) := by
    have := hq i
    exact epi_of_epi_fac (by simp [a] :
      (biprod.inl : P i ⟶ X i) ≫ a.f i = q i)
  let hh (i j : ℤ) : D.X i ⟶ D.X j :=
    if hij : j + 1 = i then
      biprod.snd ≫ eqToHom (by congr 1; omega) ≫ biprod.inl
    else 0
  have hcontract : Homotopy (𝟙 D) 0 := by
    refine { hom := hh, zero := ?_, comm := ?_ }
    · intro i j hij
      exact dite_eq_right hij
    · intro i
      rw [dNext_eq hh (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
        prevD_eq hh (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
      have hi' : i - 1 + 1 = i := by omega
      simp only [D, dd, hh, dite_eq_left rfl, dite_eq_left hi', HomologicalComplex.id_f,
        HomologicalComplex.zero_f, Category.assoc, biprod.inr_snd_assoc,
        biprod.inl_fst_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        add_zero]
      exact (biprod.total (X := P i) (Y := P (i - 1))).symm
  let F := E ⊞ D
  let s : E ⟶ F := biprod.inl
  let g : F ⟶ H := biprod.desc f a
  let e : HomotopyEquiv E F :=
    { hom := s
      inv := biprod.fst
      homotopyHomInvId := Homotopy.ofEq (by simp [s])
      homotopyInvHomId := by
        let h₁ := (hcontract.compRight (biprod.inr : D ⟶ F)).compLeft
          (biprod.snd : F ⟶ D)
        let h₂ := (Homotopy.refl (biprod.fst ≫ s)).add h₁
        exact (Homotopy.ofEq (by simp [s])).trans
          (h₂.symm.trans (Homotopy.ofEq (by
            simpa only [s, Category.id_comp] using biprod.total (X := E) (Y := D)))) }
  refine ⟨F, g, e, ?_, ?_, ?_⟩
  · intro i
    exact ObjectProperty.prop_of_iso _ (HomologicalComplex.biprodXIso E D i).symm
      (flat_biprod_kfg (hflat i) (flat_biprod_kfg (hP i) (hP (i - 1))))
  · intro i
    have := ha i
    exact epi_of_epi_fac (HomologicalComplex.biprod_inr_desc_f f a i)
  · simp [e, s, g]

set_option synthInstance.maxSize 1024 in
/-- Every complex has a K-flat resolution with flat terms and degreewise epimorphic
augmentation. The site object and morphism universes are independent.
Source: Stacks Tag 06YS (blueprint: lem-pc-kflat-resolution).
Proof:
1. Sheafify the presheaf freely generated by the sections of a module. Evaluation
shows that the free presheaf is flat, and the monoidal sheafification adjunction
transfers flatness to the sheafification. The evaluation maps give a functorial
flat epimorphic cover. Free sheaves on representables give a separating family;
exact filtered colimits and the tensor-hom adjunction supply the other hypotheses
of the source library's generic flat-resolution theorem. These constructions use
coefficients in max u v and do not identify the two site universes.
2. Apply `exists_quasiIso_flat_kFlat` to obtain a quasi-isomorphism P → G with
flat terms and categorical K-flatness. Choose flat covers Q_i → G^i. The complex
D^i = Q_i ⊕ Q_(i-1), with differential the identity from its first summand to the
next second summand, is explicitly contractible. Its map to G has components
given by the covers and their composites with the differential of G, hence is epi.
3. Set K = P ⊕ D and use the sum of the two augmentations. The inclusion of P
is a homotopy equivalence, so K remains K-flat and the new augmentation is a
quasi-isomorphism. Its components are epi and its terms are finite sums of flat
objects. Finally apply categorical K-flatness to the quasi-isomorphism 0 → Z
for an acyclic complex Z to obtain precisely `IsAcyclicTensorKFlat K`. -/
theorem exists_isKFlatResolutionGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    (G : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
      (f : K ⟶ G), CochainComplex.IsAcyclicTensorKFlat K ∧
        (∀ i : ℤ, exactFunctor _ _
          (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i))) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  classical
  let A := SheafOfModules.{max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  let := SheafOfModules.monoidalPreadditive_kfg R
  let := SheafOfModules.isGrothendieckAbelian_kfg R
  let := SheafOfModules.hasFunctorialFlatResolution_kfg R
  obtain ⟨P, p, hp, hflat, hP⟩ := exists_quasiIso_flat_kFlat G
  have hcover (M : A) : ∃ (Q : A) (q : Q ⟶ M), ObjectProperty.flat Q ∧ Epi q := by
    obtain ⟨Λ⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution A)
    exact ⟨(Λ.F.obj M).obj, Λ.π.app M, (Λ.F.obj M).property, inferInstance⟩
  obtain ⟨F, f, e, hF, hepi, hcomp⟩ := flat_epicification_kfg hcover P G p hflat
  have hkF : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat F := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hP ⊢
    exact ObjectProperty.prop_of_iso _ (HomotopyCategory.isoOfHomotopyEquiv e) hP
  have hf : QuasiIso f := by
    have : QuasiIso e.hom := e.quasiIso_hom
    have : QuasiIso (e.hom ≫ f) := by rw [hcomp]; exact hp
    exact quasiIso_of_comp_left e.hom f
  refine ⟨F, f, ?_, fun i ↦ (hF i).2, hf, hepi⟩
  intro Z hZ
  let T := MonoidalCategory.tensorRight F
  have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hkF.2 _ hz
  have htzero : (T.obj (0 : CochainComplex A ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)

end CochainComplex
