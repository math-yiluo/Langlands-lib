/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # K-flat resolutions without identifying the site universes

Source: Stacks Project, Cohomology on Sites, Tag 06YS
(blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe r u v w

open CategoryTheory MonoidalCategory Limits Opposite
open scoped ZeroObject

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  {M P N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)}

private theorem locallySmall_kfi {S : Cᵒᵖ ⥤ RingCat.{r}} :
    LocallySmall.{r} (PresheafOfModules.{r} S) := by
  let F := (toPresheaf.{r} S) ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{r}).obj (equivSmallModel.{r} C).inverse.op
  exact locallySmall_of_faithful F

private local instance small_hom_kfi {S : Cᵒᵖ ⥤ RingCat.{r}}
    (M N : PresheafOfModules.{r} S) : Small.{r} (M ⟶ N) := by
  have := locallySmall_kfi.{r, u, v} (S := S)
  infer_instance

private local instance essentiallySmall_over_kfi (X : C) : EssentiallySmall.{r} (Over X) :=
  CostructuredArrow.essentiallySmall (S := 𝟭 C) (T := X)

private noncomputable def shrink_kfi {S : Cᵒᵖ ⥤ RingCat.{r}}
    (F : PresheafOfModules.{w} S) [∀ X, Small.{r} (F.obj X)] :
    PresheafOfModules.{r} S where
  obj X := ModuleCat.of (S.obj X) (Shrink.{r} (F.obj X))
  map {X Y} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (S.map g).hom).obj
      (ModuleCat.of (S.obj Y) (Shrink.{r} (F.obj Y))))
    { toFun := fun (φ : Shrink.{r} (F.obj X)) ↦  (Shrink.linearEquiv (S.obj Y) (F.obj Y)).symm
        (F.map g ((Shrink.linearEquiv (S.obj X) (F.obj X)) φ))
      map_add' φ ψ := by rw [map_add, map_add, map_add]
      map_smul' a φ := by
        change (Shrink.linearEquiv (S.obj Y) (F.obj Y)).symm
            (F.map g ((Shrink.linearEquiv (S.obj X) (F.obj X)) (a • φ))) =
          (S.map g a) • (Shrink.linearEquiv (S.obj Y) (F.obj Y)).symm
            (F.map g ((Shrink.linearEquiv (S.obj X) (F.obj X)) φ))
        rw [map_smul, F.map_smul, map_smul] }
  map_id X := by
    ext φ : 2
    change (equivShrink.{r} (F.obj X))
      (F.map (𝟙 X) ((equivShrink.{r} (F.obj X)).symm φ)) = φ
    rw [F.map_id]
    exact Equiv.apply_symm_apply _ _
  map_comp {X Y Z} f g := by
    ext φ : 2
    change (equivShrink.{r} (F.obj Z))
        (F.map (f ≫ g) ((equivShrink.{r} (F.obj X)).symm φ)) =
      (equivShrink.{r} (F.obj Z))
        (F.map g ((equivShrink.{r} (F.obj Y)).symm
          ((equivShrink.{r} (F.obj Y))
            (F.map f ((equivShrink.{r} (F.obj X)).symm φ)))))
    rw [Equiv.symm_apply_apply, F.map_comp_apply]

private noncomputable def shrinkEquiv_kfi {S : Cᵒᵖ ⥤ RingCat.{r}}
    (F : PresheafOfModules.{w} S) [∀ X, Small.{r} (F.obj X)] (X : Cᵒᵖ) :
    (shrink_kfi F).obj X ≃ₗ[S.obj X] F.obj X :=
  Shrink.linearEquiv _ _

omit [EssentiallySmall.{r} C] in
@[local simp]
private lemma shrinkEquiv_map_kfi {S : Cᵒᵖ ⥤ RingCat.{r}}
    (F : PresheafOfModules.{w} S) [∀ X, Small.{r} (F.obj X)]
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (φ : (shrink_kfi F).obj X) :
    shrinkEquiv_kfi F Y ((shrink_kfi F).map g φ) = F.map g (shrinkEquiv_kfi F X φ) :=
  (Shrink.linearEquiv (S.obj Y) (F.obj Y)).apply_symm_apply _

private local instance small_homObj_kfi (M N : PresheafOfModules.{r} (R ⋙ forget₂ _ _))
    (X : Cᵒᵖ) : Small.{r} ((homObj M N).obj X) :=
  small_hom_kfi _ _

private noncomputable def homObjSmall_kfi
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{r} (R ⋙ forget₂ _ _) :=
  shrink_kfi (homObj M N)

variable (M) in
private noncomputable def tmulRight_kfi {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

omit [EssentiallySmall.{r} C] in
@[local simp]
private lemma tmulRight_apply_kfi {X : Cᵒᵖ} (p : P.obj X) (m : M.obj X) :
    tmulRight_kfi M p m = m ⊗ₜ[R.obj X] p :=
  rfl

private noncomputable def tensorHomCurryApp_kfi (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight_kfi M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
  naturality {W W'} f := by
    let : Module (R.obj (op W'.unop.left))
        ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map
          f.unop.left.op).hom).obj (M.obj (op W'.unop.left))) :=
      inferInstanceAs (Module (R.obj (op W'.unop.left)) (M.obj (op W'.unop.left)))
    ext m
    refine (congrArg (φ.app (op W'.unop.left)) ?_).trans
      (naturality_apply φ f.unop.left.op (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p))
    refine (congrArg (fun q : P.obj (op W'.unop.left) ↦
      M.map f.unop.left.op m ⊗ₜ[R.obj (op W'.unop.left)] q) ?_).trans
        (PresheafOfModules.Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    rw [← map_comp_apply, ← op_comp, Over.w]

omit [EssentiallySmall.{r} C] in
@[local simp]
private lemma tensorHomCurryApp_app_apply_kfi (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp_kfi φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add_kfi (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp_kfi φ (p + p') =
      tensorHomCurryApp_kfi φ p + tensorHomCurryApp_kfi φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply_kfi,
    tensorHomCurryApp_app_apply_kfi, tensorHomCurryApp_app_apply_kfi, map_add,
    TensorProduct.tmul_add,
    map_add]

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul_kfi (φ : M ⊗ P ⟶ N) {U : C}
    (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp_kfi φ (r • p) = r • tensorHomCurryApp_kfi φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply_kfi,
    tensorHomCurryApp_app_apply_kfi, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

omit [EssentiallySmall.{r} C] in
set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map_kfi (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp_kfi (U := V) φ (P.map g.op p) =
      restrictOverMap g (tensorHomCurryApp_kfi φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply_kfi, ← map_comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def homEquivSmall_kfi
    (M N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    (homObjSmall_kfi M N).obj X ≃ₗ[R.obj X] (homObj M N).obj X :=
  shrinkEquiv_kfi (homObj M N) X

set_option backward.isDefEq.respectTransparency false in
@[local simp]
private lemma homEquivSmall_map_kfi (M N : PresheafOfModules.{r} (R ⋙ forget₂ _ _))
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (φ : (homObjSmall_kfi M N).obj X) :
    homEquivSmall_kfi M N Y ((homObjSmall_kfi M N).map g φ) =
      restrictOverMap g.unop (homEquivSmall_kfi M N X φ) :=
  shrinkEquiv_map_kfi _ g φ

private noncomputable def tensorHomCurry_kfi (φ : M ⊗ P ⟶ N) :
    P ⟶ homObjSmall_kfi M N where
  app X := ModuleCat.ofHom
    { toFun p := (homEquivSmall_kfi M N X).symm (tensorHomCurryApp_kfi φ p)
      map_add' p q := by rw [tensorHomCurryApp_add_kfi, map_add]
      map_smul' a p := by rw [tensorHomCurryApp_smul_kfi, map_smul]; rfl }
  naturality {X Y} g := by
    ext p : 2
    apply (homEquivSmall_kfi M N Y).injective
    change homEquivSmall_kfi M N Y
        ((homEquivSmall_kfi M N Y).symm (tensorHomCurryApp_kfi φ (P.map g p))) =
      homEquivSmall_kfi M N Y ((homObjSmall_kfi M N).map g
        ((homEquivSmall_kfi M N X).symm (tensorHomCurryApp_kfi φ p)))
    rw [LinearEquiv.apply_symm_apply, homEquivSmall_map_kfi,
      LinearEquiv.apply_symm_apply]
    exact tensorHomCurryApp_map_kfi φ g.unop p

@[local simp]
private lemma tensorHomCurry_app_apply_kfi (φ : M ⊗ P ⟶ N) (X : Cᵒᵖ) (p : P.obj X) :
    homEquivSmall_kfi M N X ((tensorHomCurry_kfi φ).app X p) =
      tensorHomCurryApp_kfi φ p :=
  LinearEquiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
private noncomputable def homObjEvalId_kfi (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

omit [EssentiallySmall.{r} C] in
@[local simp]
private lemma homObjEvalId_apply_apply_kfi (U : C)
    (φ : (homObj M N).obj (op U)) (m : M.obj (op U)) :
    homObjEvalId_kfi M N U φ m = φ.app (op (Over.mk (𝟙 U))) m :=
  rfl

private noncomputable def tensorHomUncurry_kfi (ψ : P ⟶ homObjSmall_kfi M N) :
    M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((((homObjEvalId_kfi M N X.unop).comp
      (homEquivSmall_kfi M N X).toLinearMap).comp (ψ.app X).hom).flip))
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    have hn := congrArg (homEquivSmall_kfi M N Y) (naturality_apply ψ f p)
    change homEquivSmall_kfi M N Y ((ψ.app Y) (P.map f p)) =
      homEquivSmall_kfi M N Y ((homObjSmall_kfi M N).map f ((ψ.app X) p)) at hn
    rw [homEquivSmall_map_kfi] at hn
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶
        (restrictOver R Y.unop).obj N ↦
          ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) hn).trans ?_
    refine (restrictOver_hom_app_congr (homEquivSmall_kfi M N X (ψ.app X p))
      (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (homEquivSmall_kfi M N X (ψ.app X p))
      (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

@[local simp]
private lemma tensorHomUncurry_app_tmul_kfi (ψ : P ⟶ homObjSmall_kfi M N) (X : Cᵒᵖ)
    (m : M.obj X) (p : P.obj X) :
    (tensorHomUncurry_kfi ψ).app X (m ⊗ₜ[R.obj X] p) =
      (homEquivSmall_kfi M N X (ψ.app X p)).app (op (Over.mk (𝟙 X.unop))) m :=
  rfl

private noncomputable def homObjEquiv_kfi
    (M P N : PresheafOfModules.{r} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObjSmall_kfi M N) where
  toFun := tensorHomCurry_kfi
  invFun := tensorHomUncurry_kfi
  left_inv φ := by
    ext X : 1
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    change (homEquivSmall_kfi M N X ((tensorHomCurry_kfi φ).app X p)).app
      (op (Over.mk (𝟙 X.unop))) m = φ.app X (m ⊗ₜ[R.obj X] p)
    rw [tensorHomCurry_app_apply_kfi]
    refine congrArg (fun q : P.obj X ↦ φ.app X (m ⊗ₜ[R.obj X] q))
      (?_ : P.map (𝟙 X) p = p)
    rw [map_id]
    rfl
  right_inv ψ := by
    ext X : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
    apply (homEquivSmall_kfi M N X).injective
    rw [tensorHomCurry_app_apply_kfi]
    refine hom_ext (M₁ := (restrictOver R X.unop).obj M)
      (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
    simp only [tensorHomCurryApp_app_apply_kfi, tensorHomUncurry_app_tmul_kfi]
    have hn := congrArg (homEquivSmall_kfi M N (op W.unop.left))
      (naturality_apply ψ W.unop.hom.op p)
    change homEquivSmall_kfi M N (op W.unop.left) (ψ.app _ (P.map W.unop.hom.op p)) =
      homEquivSmall_kfi M N (op W.unop.left)
        ((homObjSmall_kfi M N).map W.unop.hom.op (ψ.app X p)) at hn
    rw [homEquivSmall_map_kfi] at hn
    refine (congrArg (fun ξ : (restrictOver R W.unop.left).obj M ⟶
        (restrictOver R W.unop.left).obj N ↦
          ξ.app (op (Over.mk (𝟙 W.unop.left))) m) hn).trans ?_
    exact restrictOver_hom_app_congr (homEquivSmall_kfi M N X (ψ.app X p))
      (Category.id_comp W.unop.hom) m

private lemma homObjEquiv_whiskerLeft_comp_kfi
    {P' : PresheafOfModules.{r} (R ⋙ forget₂ _ _)}
    (f : P ⟶ P') (φ : M ⊗ P' ⟶ N) :
    homObjEquiv_kfi M P N (M ◁ f ≫ φ) = f ≫ homObjEquiv_kfi M P' N φ := by
  ext X : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
  apply (homEquivSmall_kfi M N X).injective
  change homEquivSmall_kfi M N X ((tensorHomCurry_kfi (M ◁ f ≫ φ)).app X p) =
    homEquivSmall_kfi M N X ((tensorHomCurry_kfi φ).app X (f.app X p))
  rw [tensorHomCurry_app_apply_kfi, tensorHomCurry_app_apply_kfi]
  refine hom_ext (M₁ := (restrictOver R X.unop).obj M)
    (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun q : P'.obj (op W.unop.left) ↦
    φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] q))
      (naturality_apply f W.unop.hom.op p)

private theorem isSheaf_homObjSmall_kfi {J : GrothendieckTopology C}
    (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (homObjSmall_kfi M N).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{r})
  rw [isSheaf_iff_isSheaf_of_type]
  have hraw := Presheaf.isSheaf_comp_of_isSheaf J (homObj M N).presheaf (forget _)
    (isSheaf_homObj hN)
  rw [isSheaf_iff_isSheaf_of_type] at hraw
  apply Presieve.isSheaf_of_nat_equiv
    (fun {X} ↦ (homEquivSmall_kfi M N (op X)).symm.toEquiv) _ hraw
  intro X Y f φ
  apply (homEquivSmall_kfi M N (op X)).injective
  change homEquivSmall_kfi M N (op X)
      ((homEquivSmall_kfi M N (op X)).symm (restrictOverMap f φ)) =
    homEquivSmall_kfi M N (op X) ((homObjSmall_kfi M N).map f.op
      ((homEquivSmall_kfi M N (op Y)).symm φ))
  rw [LinearEquiv.apply_symm_apply, homEquivSmall_map_kfi,
    LinearEquiv.apply_symm_apply]
  rfl

end PresheafOfModules

namespace SheafOfModules

-- The underlying sheaf of rings of the sheaf of commutative rings `R`.
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

-- The sheafification functor from presheaves of modules over `R` to sheaves of modules over `R`.
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{r} (𝟙 (𝓡).obj)

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {R : Sheaf J CommRingCat.{r}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory

private noncomputable def homObjSmall_kfi (A N : SheafOfModules.{r} 𝓡) :
    SheafOfModules.{r} 𝓡 where
  val := PresheafOfModules.homObjSmall_kfi A.val N.val
  isSheaf := PresheafOfModules.isSheaf_homObjSmall_kfi N.isSheaf

-- The tensor localization comparison has dependent sheafification instances.
/-- The tensor comparison is natural in the second factor. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom_kfi (A : SheafOfModules.{r} 𝓡)
    {T T' : SheafOfModules.{r} 𝓡} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫ (𝓢).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (𝓡).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- **The tensor-hom adjunction for sheaves of modules**: morphisms `A ⊗ T ⟶ N` correspond to
morphisms `T ⟶ homObjSmall_kfi A N`. A morphism `A ⊗ T ⟶ N` is a morphism `a(A ⊗ T) ⟶ N` out of the
sheafification of the presheaf tensor product, i.e. a morphism of presheaves `A ⊗ T ⟶ N`, which
`PresheafOfModules.homObjEquiv` turns into a morphism `T ⟶ homObjSmall_kfi A N`. -/
private noncomputable def tensorHomEquiv_kfi (A T N : SheafOfModules.{r} 𝓡) :
    (A ⊗ T ⟶ N) ≃ (T ⟶ homObjSmall_kfi A N) where
  toFun φ := ⟨PresheafOfModules.homObjEquiv_kfi (R := R.obj) A.val T.val N.val
    ((PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (𝓡).obj)).homEquiv _ N
      ((tensorObjIsoSheafification A T).inv ≫ φ))⟩
  invFun ψ := (tensorObjIsoSheafification A T).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (𝓡).obj)).homEquiv _ N).symm
      ((PresheafOfModules.homObjEquiv_kfi (R := R.obj) A.val T.val N.val).symm ψ.val)
  left_inv φ := by simp
  right_inv ψ := by
    ext1
    dsimp only
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private lemma tensorHomEquiv_val_kfi (A T N : SheafOfModules.{r} 𝓡) (φ : A ⊗ T ⟶ N) :
    (tensorHomEquiv_kfi A T N φ).val =
      PresheafOfModules.homObjEquiv_kfi (R := R.obj) A.val T.val N.val
      ((PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (𝓡).obj)).homEquiv _ N
        ((tensorObjIsoSheafification A T).inv ≫ φ)) :=
  rfl

/-- The tensor-hom adjunction for sheaves of modules is natural in `T`. -/
private lemma tensorHomEquiv_whiskerLeft_comp_kfi (A : SheafOfModules.{r} 𝓡)
    {T T' N : SheafOfModules.{r} 𝓡}
    (f : T ⟶ T') (φ : A ⊗ T' ⟶ N) :
    tensorHomEquiv_kfi A T N (A ◁ f ≫ φ) = f ≫ tensorHomEquiv_kfi A T' N φ := by
  have h : (tensorObjIsoSheafification A T).inv ≫ A ◁ f =
      (𝓢).map (A.val ◁ f.val) ≫ (tensorObjIsoSheafification A T').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_tensorObjIsoSheafification_hom_kfi,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext1
  rw [comp_val, tensorHomEquiv_val_kfi, tensorHomEquiv_val_kfi, ← Category.assoc, h, Category.assoc,
    Adjunction.homEquiv_naturality_left]
  exact PresheafOfModules.homObjEquiv_whiskerLeft_comp_kfi _ _

@[no_expose, irreducible]
private noncomputable def monoidalClosed_kfi : MonoidalClosed (SheafOfModules.{r} 𝓡) where
  closed A :=
    { rightAdj := Adjunction.rightAdjointOfEquiv (F := tensorLeft A)
        (G_obj := homObjSmall_kfi A) (tensorHomEquiv_kfi A)
        (fun _ _ _ f g ↦ tensorHomEquiv_whiskerLeft_comp_kfi A f g)
      adj := Adjunction.adjunctionOfEquivRight (F := tensorLeft A)
        (G_obj := homObjSmall_kfi A) (tensorHomEquiv_kfi A)
        (fun _ _ _ f g ↦ tensorHomEquiv_whiskerLeft_comp_kfi A f g) }

/-- The sheafified tensor is closed at independent site and coefficient universes.
Source: Stacks Project, Modules on Sites, Tag 03EO
(blueprint: lem-pc-sheaf-modules-tensor-closed).

Proof: the already constructed small internal Hom represents the tensor-Hom
adjunction. Package that adjunction as the existing closed monoidal structure. -/
theorem nonempty_monoidalClosed_independentCoefficients :
    Nonempty (MonoidalClosed (SheafOfModules.{r} 𝓡)) :=
  ⟨monoidalClosed_kfi⟩

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "O" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{r} O

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory monoidalClosed_kfi

private theorem monoidalPreadditive_kfi : MonoidalPreadditive A := by
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

private noncomputable def tensorSheafificationIso_kfi
    (F : PresheafOfModules.{r} (O).obj) :
    tensorRight ((PresheafOfModules.sheafification.{r} (𝟙 (O).obj)).obj F) ≅
      (SheafOfModules.forget.{r} O ⋙
        PresheafOfModules.restrictScalars (𝟙 (O).obj)) ⋙ tensorRight F ⋙
        PresheafOfModules.sheafification.{r} (𝟙 (O).obj) := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight a F)

/-- The canonical free-presheaf cover gives functorial categorical flat resolutions.
Source: Stacks Project, Tag 03EW; used for the independent-coefficient K-flat resolution
(blueprint: lem-pc-kflat-resolution). -/
theorem hasFunctorialFlatResolution_kfi : Abelian.HasFunctorialFlatResolution A := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{r} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{r} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{r} (O).obj
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
  have hτ (M : PresheafOfModules.{r} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
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
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_kfi R (G.obj (V.obj M))).symm
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

private theorem hasExactColimits_int_kfi [HasSheafify J AddCommGrpCat.{r}] :
    HasExactColimitsOfShape ℤ A := by
  have := AB5OfSize_of_univLE.{0, 0, r, r} AddCommGrpCat.{r}
  exact HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf.{r} O)

end SheafOfModules

namespace CochainComplex

private theorem flat_biprod_kfi
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [HasCountableCoproducts A]
    {M N : A} (hM : ObjectProperty.flat M) (hN : ObjectProperty.flat N) :
    ObjectProperty.flat (M ⊞ N) := by
  apply ObjectProperty.prop_of_iso _ (biprod.isoProd M N).symm
  exact ObjectProperty.prop_of_isLimit _ (limit.isLimit (pair M N))
    (by rintro ⟨_ | _⟩ <;> assumption)

private theorem flat_epicification_kfi
    {A : Type*} [Category A] [Abelian A] [MonoidalCategory A] [MonoidalPreadditive A]
    [MonoidalClosed A] [BraidedCategory A] [HasCountableCoproducts A]
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
      (flat_biprod_kfi (hflat i) (flat_biprod_kfi (hP i) (hP (i - 1))))
  · intro i
    have := ha i
    exact epi_of_epi_fac (HomologicalComplex.biprod_inr_desc_f f a i)
  · simp [e, s, g]


set_option synthInstance.maxSize 1024 in
/-- Every complex has a K-flat resolution with flat terms and degreewise epimorphic
augmentation. The site object and morphism universes are independent.
Source: Stacks Tag 06YS (blueprint: lem-pc-kflat-resolution).
Proof:
1. Choose the strictly compatible bounded-above flat replacement tower of the good
truncations, with degreewise epimorphic quasi-isomorphisms q_n
(lem-pc-flat-truncation-tower).
2. On B, the countable sum of the replacements, let φ be one minus the tower shift and
let s be the sum of q_n followed by the truncation inclusions. Compatibility gives φ ≫ s = 0.
The cone desc construction, with shifted component zero and unshifted component s, gives
f : Cone(φ) ⟶ G. The telescope is K-flat by lem-pc-kflat-closure. Evaluation preserves
coproducts; their terms and the finite sums forming the cone terms are flat by the same
closure lemma. Reindex countable sums by ULift into r, without changing the site.
3. The cone desc restrictions satisfy lem-pc-flat-truncation-telescope-comparison, so f is
a quasi-isomorphism. In degree i choose n = i.toNat + 1. The truncation inclusion is an
isomorphism in that degree, so its composite with q_n is epi. This composite factors
through f in degree i, proving the required degreewise epimorphic augmentation. -/
theorem exists_isKFlatResolutionIndependentCoefficients
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R : Sheaf J CommRingCat.{r}}
    (G : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    ∃ (K : CochainComplex (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (f : K ⟶ G), CochainComplex.IsKFlatIndependentCoefficients K ∧
        (∀ i : ℤ, exactFunctor _ _
          (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i))) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  -- Use the reduced left-resolution API with exact integer-indexed colimits.
  -- Shrinking the internal hom supplies closedness at independent coefficient universes;
  -- contractible disks supply degreewise epimorphisms.
  classical
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have (K : Type r) : HasColimitsOfShape (Discrete K) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  have (K : Type r) : HasColimitsOfShape (Discrete K) A :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  have : HasFiniteBiproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := A)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have hres : ∃ (P : CochainComplex A ℤ) (p : P ⟶ G),
      QuasiIso p ∧ (∀ n, ObjectProperty.flat (P.X n)) ∧
        (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P := by
    have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
      preservesColimitsOfShape_of_natIso (F := tensorLeft X)
        (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
    let Λ := (Classical.arbitrary (Abelian.LeftResolution
      (ObjectProperty.flat.ι : _ ⥤ A))).reduced
    have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat := by
      rintro X ⟨Y, ⟨e⟩⟩
      exact ObjectProperty.prop_of_iso _ e Y.property
    refine ⟨Λ.resolutionFunctor.obj G, Λ.resolutionNatTrans.app G,
      inferInstance, fun n ↦ ?_, Λ.kFlat_resolutionFunctor_obj hι G⟩
    have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj G
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n) c.isColimit)
      (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
  obtain ⟨P, p, hp, hflat, hP⟩ := hres
  have hcover (M : A) : ∃ (Q : A) (q : Q ⟶ M), ObjectProperty.flat Q ∧ Epi q := by
    obtain ⟨Λ⟩ := (inferInstance : Abelian.HasFunctorialFlatResolution A)
    exact ⟨(Λ.F.obj M).obj, Λ.π.app M, (Λ.F.obj M).property, inferInstance⟩
  obtain ⟨F, f, e, hF, hepi, hcomp⟩ := flat_epicification_kfi hcover P G p hflat
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
