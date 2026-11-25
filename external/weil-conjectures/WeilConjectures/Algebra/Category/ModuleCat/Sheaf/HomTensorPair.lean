/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat

/-!
# Currying a pair of sheaf evaluations

Source: Stacks Project, Modules on Sites, Lemma 03EO, and Cohomology on Sites, Tag 0A90.
(blueprint: lem-sc-hom-tensor-pair-construction)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {A M P N : PresheafOfModules.{max u v} (R ⋙ forget₂ _ _)}

variable (M) in
private noncomputable def tmulRight_pair {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

private noncomputable def tensorHomCurryApp_pair (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U)) :
    (restrictOver R U).obj M ⟶ (restrictOver R U).obj N where
  app W := tmulRight_pair M (P.map W.unop.hom.op p) ≫ φ.app (op W.unop.left)
  naturality {W W'} f := by
    ext m
    refine (congrArg (φ.app (op W'.unop.left)) ?_).trans
      (naturality_apply φ f.unop.left.op (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p))
    refine (congrArg (fun q : P.obj (op W'.unop.left) ↦
      (show M.obj (op W'.unop.left) from M.map f.unop.left.op m)
        ⊗ₜ[R.obj (op W'.unop.left)] q) ?_).trans
        (Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    rw [← map_comp_apply, ← op_comp, Over.w]

@[local simp]
private lemma tensorHomCurryApp_app_apply_pair (φ : M ⊗ P ⟶ N) {U : C}
    (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp_pair φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add_pair (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp_pair φ (p + p') =
      tensorHomCurryApp_pair φ p + tensorHomCurryApp_pair φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply_pair,
    tensorHomCurryApp_app_apply_pair, tensorHomCurryApp_app_apply_pair,
    map_add, TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul_pair (φ : M ⊗ P ⟶ N) {U : C}
    (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp_pair φ (r • p) = r • tensorHomCurryApp_pair φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply_pair,
    tensorHomCurryApp_app_apply_pair, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map_pair (φ : M ⊗ P ⟶ N) {U V : C} (g : V ⟶ U) (p : P.obj (op U)) :
    tensorHomCurryApp_pair (U := V) φ (P.map g.op p) =
      restrictOverMap g (tensorHomCurryApp_pair φ p) := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [restrictOverMap_app, tensorHomCurryApp_app_apply_pair, ← map_comp_apply]
  rfl

private noncomputable def tensorHomCurry_pair (φ : M ⊗ P ⟶ N) : P ⟶ homObj M N where
  app X := ModuleCat.ofHom (X := P.obj X) (Y := (homObj M N).obj X)
    { toFun p := tensorHomCurryApp_pair φ p
      map_add' := tensorHomCurryApp_add_pair φ
      map_smul' := tensorHomCurryApp_smul_pair φ }
  naturality {X Y} g := by
    ext p : 2
    exact tensorHomCurryApp_map_pair φ g.unop p

set_option backward.isDefEq.respectTransparency false in
variable (M N) in
private noncomputable def homObjEvalId_pair (U : C) :
    (homObj M N).obj (op U) →ₗ[R.obj (op U)] M.obj (op U) →ₗ[R.obj (op U)] N.obj (op U) where
  toFun φ := (φ.app (op (Over.mk (𝟙 U)))).hom
  map_add' _ _ := rfl
  map_smul' r φ := by
    ext m
    rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, sectionsSMul_app_apply,
      overSections_coe_apply]
    simp

private noncomputable def tensorHomUncurry_pair (ψ : P ⟶ homObj M N) : M ⊗ P ⟶ N where
  app X := ModuleCat.ofHom
    (TensorProduct.lift ((homObjEvalId_pair M N X.unop).comp (ψ.app X).hom).flip)
  naturality {X Y} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine (congrArg (fun ξ : (restrictOver R Y.unop).obj M ⟶ (restrictOver R Y.unop).obj N ↦
      ξ.app (op (Over.mk (𝟙 Y.unop))) (M.map f m)) (naturality_apply ψ f p)).trans ?_
    refine (restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp f.unop) (M.map f m)).trans ?_
    exact naturality_apply (ψ.app X p) (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 _)).op m

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pairing (f : A ⟶ homObj M N) (U : Cᵒᵖ)
    (a : A.obj U) (m : M.obj U) : N.obj U :=
  (f.app U a).app (op (Over.mk (𝟙 U.unop))) m

set_option backward.isDefEq.respectTransparency false in
private lemma pairing_natural (f : A ⟶ homObj M N) {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : A.obj U) (m : M.obj U) :
    N.map g (pairing f U a m) = pairing f V (A.map g a) (M.map g m) := by
  have h := naturality_apply (f.app U a)
    (Over.homMk g.unop : Over.mk g.unop ⟶ Over.mk (𝟙 U.unop)).op m
  have hf := naturality_apply f g a
  dsimp only [homObj_map_apply] at hf
  dsimp only [pairing]
  rw [hf]
  exact h.symm.trans
    (restrictOver_hom_app_congr (f.app U a) (Category.id_comp g.unop).symm _)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transposeApp (f : A ⟶ homObj M N) {U : C}
    (m : M.obj (op U)) : (restrictOver R U).obj A ⟶ (restrictOver R U).obj N where
  app W := ModuleCat.ofHom
    { toFun := fun a ↦ pairing f (op W.unop.left) a (M.map W.unop.hom.op m)
      map_add' := by
        intro a b
        dsimp only [pairing]
        rw [map_add]
        rw [add_app]
        rfl
      map_smul' := by
        intro r a
        dsimp only [pairing]
        rw [map_smul]
        rw [smul_app]
        change R.map (𝟙 W.unop.left).op r •
          pairing f (op W.unop.left) a (M.map W.unop.hom.op m) =
            r • pairing f (op W.unop.left) a (M.map W.unop.hom.op m)
        simp }
  naturality {W W'} g := by
    ext a
    change pairing f (op W'.unop.left) (A.map g.unop.left.op a)
      (M.map W'.unop.hom.op m) =
        N.map g.unop.left.op
          (pairing f (op W.unop.left) a (M.map W.unop.hom.op m))
    rw [pairing_natural]
    congr 1
    rw [← map_comp_apply, ← op_comp, Over.w]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transpose (f : A ⟶ homObj M N) : M ⟶ homObj A N where
  app U := ModuleCat.ofHom (Y := (homObj A N).obj U)
    { toFun := transposeApp f
      map_add' := by
        intro m n
        apply hom_ext
        intro W
        ext a
        rw [add_app]
        change pairing f _ a (M.map W.unop.hom.op (m + n)) =
          pairing f _ a (M.map W.unop.hom.op m) + pairing f _ a (M.map W.unop.hom.op n)
        dsimp only [pairing]
        rw [(M.map W.unop.hom.op).hom.map_add, map_add]
      map_smul' := by
        intro r m
        apply hom_ext
        intro W
        ext a
        rw [smul_app]
        change pairing f _ a (M.map W.unop.hom.op (r • m)) =
          R.map W.unop.hom.op r • pairing f _ a (M.map W.unop.hom.op m)
        dsimp only [pairing]
        rw [M.map_smul, map_smul]
        rfl }
  naturality {U V} g := by
    ext m : 2
    apply hom_ext
    intro W
    ext a
    change pairing f (op W.unop.left) a
      (M.map W.unop.hom.op (M.map g m)) =
        pairing f (op W.unop.left) a
          (M.map (W.unop.hom ≫ g.unop).op m)
    rw [← map_comp_apply]
    rfl

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification extension agrees with its prescribed presheaf map on the unit.
Source: the module sheafification adjunction and the tensor comparison inverse law. -/
private theorem tensorLift_unit (A B N : Mod) (q : A.val ⊗ B.val ⟶ N.val) :
    let := monoidalCategory R
    let adj := PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
    let k : A ⊗ B ⟶ N :=
      (tensorObjIsoSheafification (R := R) A B).hom ≫ (adj.homEquiv _ _).symm q
    (adj.unit.app (A.val ⊗ B.val) ≫
      (tensorObjIsoSheafification (R := R) A B).inv.val) ≫ k.val = q := by
  let := monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have hi : (tensorObjIsoSheafification (R := R) A B).inv.val ≫
      (tensorObjIsoSheafification (R := R) A B).hom.val =
        𝟙 ((PresheafOfModules.sheafification
          (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).obj
            (A.val ⊗ B.val)).val := by
    exact congrArg SheafOfModules.Hom.val
      (tensorObjIsoSheafification (R := R) A B).inv_hom_id
  have hq := (adj.homEquiv (A.val ⊗ B.val) N).apply_symm_apply q
  change adj.unit.app (A.val ⊗ B.val) ≫
    ((adj.homEquiv (A.val ⊗ B.val) N).symm q).val = q at hq
  change (adj.unit.app (A.val ⊗ B.val) ≫
    (tensorObjIsoSheafification (R := R) A B).inv.val) ≫
    (tensorObjIsoSheafification (R := R) A B).hom.val ≫
      ((adj.homEquiv (A.val ⊗ B.val) N).symm q).val = q
  rw [Category.assoc, ← Category.assoc
    (tensorObjIsoSheafification (R := R) A B).inv.val, hi, Category.id_comp]
  exact hq

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency false in
/-- Two sheaf evaluations factor through the tensor of their inputs.
Source: Stacks Project, Modules on Sites, Lemma internal-hom-adjoint-tensor (Tag 03EO),
and Cohomology on Sites, Lemma sites-cohomology-lemma-compose (Tag 0A90).
(blueprint: lem-sc-hom-tensor-pair-construction).

Proof: Uncurry the underlying presheaf maps f and g by the balanced tensor
universal property. Braiding and associativity order the three inputs as y, x, s;
the resulting presheaf map sends s tensor (x tensor y) to g(f(s)(x))(y).
Curry in s to obtain a presheaf tensor map A.val tensor B.val into homObj S D,
which is a sheaf. Extend it uniquely through module sheafification and the tensor
comparison to a sheaf map k from A tensor B into homObj S D. Transpose its local
bilinear pairing to obtain b. The sheafification adjunction identifies k on the
unit's pure tensors with the presheaf map. Naturality of f identifies its value
on the restriction of s at the identity slice object with f(s) at W, giving the
formula. The constructions use sectionwise linear maps in separate site universes;
no complex, infinite product, or coproduct is involved. -/
theorem homTensorPair_construct (S A H B D : Mod)
    (f : S ⟶ homObj (R := R) A H) (g : H ⟶ homObj (R := R) B D) :
    let := monoidalCategory R
    ∃ b : S ⟶ homObj (R := R) (A ⊗ B) D,
      ∀ (U : Cᵒᵖ) (s : S.val.obj U) (W : (Over U.unop)ᵒᵖ)
        (x : A.val.obj (op W.unop.left)) (y : B.val.obj (op W.unop.left)),
        (((b.val.app U).hom s).app W).hom
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
              (A.val ⊗ B.val) ≫ (tensorObjIsoSheafification (R := R) A B).inv.val).app
                (op W.unop.left) |>.hom (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
        ((((g.val.app (op W.unop.left)).hom
          ((((f.val.app U).hom s).app W).hom x)).app
            (op (Over.mk (𝟙 W.unop.left)))).hom y) := by
  classical
  let := monoidalCategory R
  let f' := PresheafOfModules.tensorHomUncurry_pair f.val
  let g' := PresheafOfModules.tensorHomUncurry_pair g.val
  let φ : S.val ⊗ (A.val ⊗ B.val) ⟶ D.val :=
    (β_ S.val (A.val ⊗ B.val)).hom ≫
      ((β_ A.val B.val).hom ▷ S.val) ≫
        (α_ B.val A.val S.val).hom ≫ (B.val ◁ f') ≫ g'
  let q : A.val ⊗ B.val ⟶ (homObj (R := R) S D).val :=
    PresheafOfModules.tensorHomCurry_pair φ
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let k : A ⊗ B ⟶ homObj (R := R) S D :=
    (tensorObjIsoSheafification (R := R) A B).hom ≫ (adj.homEquiv _ _).symm q
  let b : S ⟶ homObj (R := R) (A ⊗ B) D :=
    ⟨PresheafOfModules.transpose k.val⟩
  refine ⟨b, ?_⟩
  intro U s W x y
  let V := op W.unop.left
  let τ := adj.unit.app (A.val ⊗ B.val) ≫
    (tensorObjIsoSheafification (R := R) A B).inv.val
  have hk : τ ≫ k.val = q :=
    tensorLift_unit R A B (homObj (R := R) S D) q
  have he := congrArg
    (fun z : A.val ⊗ B.val ⟶ (homObj (R := R) S D).val ↦
      ((z.app V).hom (x ⊗ₜ[R.obj.obj V] y)).app
        (op (Over.mk (𝟙 W.unop.left))) |>.hom (S.val.map W.unop.hom.op s)) hk
  change ((((k.val.app V).hom ((τ.app V).hom (x ⊗ₜ[R.obj.obj V] y))).app
    (op (Over.mk (𝟙 W.unop.left)))).hom (S.val.map W.unop.hom.op s)) = _
  refine he.trans ?_
  change (φ.app V).hom
    ((S.val.map W.unop.hom.op s) ⊗ₜ[R.obj.obj V]
      (A.val.map (𝟙 W.unop.left).op x ⊗ₜ[R.obj.obj V]
        B.val.map (𝟙 W.unop.left).op y)) = _
  have hx : A.val.map (𝟙 W.unop.left).op x = x := by
    rw [op_id, PresheafOfModules.map_id]
    rfl
  have hy : B.val.map (𝟙 W.unop.left).op y = y := by
    rw [op_id, PresheafOfModules.map_id]
    rfl
  rw [hx, hy]
  change (g'.app V).hom
    (y ⊗ₜ[R.obj.obj V] (f'.app V).hom
      (x ⊗ₜ[R.obj.obj V] S.val.map W.unop.hom.op s)) = _
  change (((g.val.app V).hom
    ((((f.val.app V).hom (S.val.map W.unop.hom.op s)).app
      (op (Over.mk (𝟙 W.unop.left)))).hom x)).app
        (op (Over.mk (𝟙 W.unop.left)))).hom y = _
  have hf := PresheafOfModules.naturality_apply f.val W.unop.hom.op s
  change (f.val.app V).hom (S.val.map W.unop.hom.op s) =
    PresheafOfModules.restrictOverMap W.unop.hom ((f.val.app U).hom s) at hf
  rw [hf]
  exact congrArg (fun z ↦ ((g.val.app V).hom z).app
    (op (Over.mk (𝟙 W.unop.left))) |>.hom y)
    (PresheafOfModules.restrictOver_hom_app_congr ((f.val.app U).hom s)
      (Category.id_comp W.unop.hom) x)

end SheafOfModules
