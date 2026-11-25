/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.HomTensorReverseConstruction
import WeilConjectures.Algebra.Homology.HomComplexProjections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Inverse to degreewise currying

Source: Stacks Project, Cohomology on Sites, Lemma 21.34.1, Tag 0A90.
(blueprint: lem-sc-hom-tensor-degreewise-iso)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

-- The source tensor-Hom API uses one universe for the site and the coefficients.
-- This private API allows an extra ambient universe `w`. Unlike the localized APIs,
-- coefficients and modules may live in `max u v w`, rather than only `max u v`.
-- The internal Hom stays in the same category.
-- Source: WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom, TensorHom.
namespace IsoTensorHom

open PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  {M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ CommRingCat RingCat)}

variable (M) in
/-- The morphism `M(X) ⟶ (M ⊗ P)(X)` sending `m` to `m ⊗ p`, for a section `p` of `P` over
`X`. -/
private noncomputable def tmulRight {X : Cᵒᵖ} (p : P.obj X) : M.obj X ⟶ (M ⊗ P).obj X :=
  ModuleCat.ofHom ((TensorProduct.mk (R.obj X) (M.obj X) (P.obj X)).flip p)

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
      (show M.obj (op W'.unop.left) from M.map f.unop.left.op m)
        ⊗ₜ[R.obj (op W'.unop.left)] q) ?_).trans
        (Monoidal.tensorObj_map_tmul f.unop.left.op m _).symm
    rw [← map_comp_apply, ← op_comp, Over.w]

@[local simp]
private lemma tensorHomCurryApp_app_apply
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    {M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (p : P.obj (op U))
    (W : (Over U)ᵒᵖ) (m : M.obj (op W.unop.left)) :
    ((tensorHomCurryApp φ p).app W).hom m =
      φ.app (op W.unop.left) (m ⊗ₜ[R.obj (op W.unop.left)] P.map W.unop.hom.op p) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_add
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    {M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (p p' : P.obj (op U)) :
    tensorHomCurryApp φ (p + p') = tensorHomCurryApp φ p + tensorHomCurryApp φ p' := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [add_app, ModuleCat.hom_add, LinearMap.add_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, tensorHomCurryApp_app_apply, map_add, TensorProduct.tmul_add,
    map_add]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_smul
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    {M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ CommRingCat RingCat)}
   (φ : M ⊗ P ⟶ N) {U : C} (r : R.obj (op U)) (p : P.obj (op U)) :
    tensorHomCurryApp φ (r • p) = r • tensorHomCurryApp φ p := by
  ext W : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
  rw [smul_app, ModuleCat.hom_comp, LinearMap.comp_apply, tensorHomCurryApp_app_apply,
    tensorHomCurryApp_app_apply, sectionsSMul_app_apply, overSections_coe_apply, map_smul]
  exact (congrArg _ (TensorProduct.tmul_smul (R.map W.unop.hom.op r) m _)).trans (map_smul _ _ _)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorHomCurryApp_map
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
    {M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ CommRingCat RingCat)}
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

/-- The tensor-hom adjunction for presheaves of modules: morphisms `M ⊗ P ⟶ N` correspond to
morphisms `P ⟶ homObj M N`. A morphism `φ : M ⊗ P ⟶ N` is sent to the morphism which sends a
section `p` of `P` over `U` to `m ↦ φ (m ⊗ p|_W)` for `W ⟶ U` and `m` a section of `M` over
`W`. -/
private noncomputable def homObjEquiv (M P N : PresheafOfModules.{max u v w} (R ⋙ forget₂ _ _)) :
    (M ⊗ P ⟶ N) ≃ (P ⟶ homObj M N) where
  toFun := tensorHomCurry
  invFun := tensorHomUncurry
  left_inv φ := by
    apply PresheafOfModules.hom_ext
    intro X
    refine ModuleCat.MonoidalCategory.tensor_ext fun m p ↦ ?_
    refine congrArg (fun q : P.obj X ↦ φ.app X (m ⊗ₜ[R.obj X] q)) (?_ : P.map (𝟙 X) p = p)
    rw [map_id]
    rfl
  right_inv ψ := by
    apply PresheafOfModules.hom_ext
    intro X
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : P.obj X) ↦ ?_)
    refine hom_ext (M₁ := (restrictOver R X.unop).obj M) (M₂ := (restrictOver R X.unop).obj N)
      fun W ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (m : M.obj (op W.unop.left)) ↦ ?_)
    refine (congrArg (fun ξ : (restrictOver R W.unop.left).obj M ⟶
        (restrictOver R W.unop.left).obj N ↦ ξ.app (op (Over.mk (𝟙 W.unop.left))) m)
      (naturality_apply ψ W.unop.hom.op p)).trans ?_
    exact restrictOver_hom_app_congr (ψ.app X p) (Category.id_comp W.unop.hom) m

end IsoTensorHom


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option backward.isDefEq.respectTransparency true in
private theorem homTerm_section_ext (L M : CochainComplex Mod ℤ) (n : ℤ)
    (U : Cᵒᵖ) (x y : ((homComplex (R := R) L M).X n).val.obj U)
    (h : ∀ p : ℤ,
      ((homTensorCurryProjection R L M n p (p + n) rfl).val.app U).hom x =
        ((homTensorCurryProjection R L M n p (p + n) rfl).val.app U).hom y) :
    x = y := by
  have hs : Nonempty (Limits.IsLimit (Limits.Fan.mk ((homComplex (R := R) L M).X n)
      (fun p : ℤ ↦ homTensorCurryProjection R L M n p (p + n) rfl))) :=
    (Classical.choose_spec
      (homComplex_projections_exists.{u, v, max u v, max u v} (R := R))).1 L M n
  apply Limits.Concrete.isLimit_ext _
    (Limits.isLimitOfPreserves (SheafOfModules.evaluation _ U) hs.some) x y
  intro p
  set_option backward.isDefEq.respectTransparency false in
    simp only [Functor.mapCone_π_app, Limits.Fan.mk_π_app,
    SheafOfModules.evaluation, Functor.comp_map, Functor.comp_obj,
    PresheafOfModules.evaluation, Discrete.functor_obj_eq_as, SheafOfModules.forget]
  exact h p.as


private theorem hom_eval_restrict {A B X : Mod}
    (f : X ⟶ SheafOfModules.homObj (R := R) A B) (U : Cᵒᵖ)
    (s : X.val.obj U) (W : (Over U.unop)ᵒᵖ)
    (x : A.val.obj (op W.unop.left)) :
    (((f.val.app U).hom s).app W).hom x =
      (((f.val.app (op W.unop.left)).hom (X.val.map W.unop.hom.op s)).app
        (op (Over.mk (𝟙 W.unop.left)))).hom x := by
  have h := PresheafOfModules.naturality_apply f.val W.unop.hom.op s
  change (f.val.app (op W.unop.left)).hom (X.val.map W.unop.hom.op s) =
    PresheafOfModules.restrictOverMap W.unop.hom ((f.val.app U).hom s) at h
  calc
    _ = ((PresheafOfModules.restrictOverMap W.unop.hom
        ((f.val.app U).hom s)).app (op (Over.mk (𝟙 W.unop.left)))).hom x := by
      exact (PresheafOfModules.restrictOver_hom_app_congr
        ((f.val.app U).hom s) (Category.id_comp W.unop.hom) x).symm
    _ = _ := congrArg (fun t ↦ (t.app (op (Over.mk (𝟙 W.unop.left)))).hom x) h.symm


private theorem homTerm_section_ext' (L M : CochainComplex Mod ℤ) (n : ℤ)
    (U : Cᵒᵖ) (x y : ((homComplex (R := R) L M).X n).val.obj U)
    (h : ∀ (p q : ℤ) (hpq : p + n = q),
      ((homTensorCurryProjection R L M n p q hpq).val.app U).hom x =
        ((homTensorCurryProjection R L M n p q hpq).val.app U).hom y) :
    x = y :=
  homTerm_section_ext R L M n U x y (fun p ↦ h p (p + n) rfl)

private theorem homTerm_hom_ext (L M : CochainComplex Mod ℤ) (n : ℤ)
    {X : Mod} (a b : X ⟶ (homComplex (R := R) L M).X n)
    (h : ∀ p : ℤ, a ≫ homTensorCurryProjection R L M n p (p + n) rfl =
      b ≫ homTensorCurryProjection R L M n p (p + n) rfl) : a = b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply homTerm_section_ext R L M n U
  intro p
  exact congrArg (fun f ↦ (f.val.app U).hom s) (h p)

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
private theorem tensorLocalized_ext
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
          (((homTensorCurrySectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (((b.val.app U).hom s).app W).hom
        (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          i j p hij).val.app (op W.unop.left)).hom
          (((homTensorCurrySectionMap R (K.X i) (L.X j)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)))) → a = b := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  intro a b h
  let T := (CochainComplex.mapBifunctor K L (curriedTensor Mod)).X p
  let flip : (X ⟶ SheafOfModules.homObj (R := R) T N) →
      (T ⟶ SheafOfModules.homObj (R := R) X N) := fun f ↦
    ⟨IsoTensorHom.homObjEquiv.{u, v, max u v} X.val T.val N.val
      ((β_ X.val T.val).hom ≫
        (IsoTensorHom.homObjEquiv.{u, v, max u v} T.val X.val N.val).symm f.val)⟩
  have hf : Function.Injective flip := by
    intro f g he
    apply SheafOfModules.hom_ext
    apply (IsoTensorHom.homObjEquiv.{u, v, max u v} T.val X.val N.val).symm.injective
    apply (cancel_epi (β_ X.val T.val).hom).1
    exact (IsoTensorHom.homObjEquiv.{u, v, max u v} X.val T.val N.val).injective
      (congrArg SheafOfModules.Hom.val he)
  apply hf
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification
    (R := R) (K.X i) (L.X j)).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).homEquiv
      ((K.X i).val ⊗ (L.X j).val) _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  dsimp only [Functor.comp_map, SheafOfModules.forget_map,
    PresheafOfModules.restrictScalars]
  change (((flip a).val.app U).hom
    (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod) i j p hij).val.app U).hom
      (((homTensorCurrySectionMap R (K.X i) (L.X j)).app U).hom
        (x ⊗ₜ[R.obj.obj U] y)))) = _
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let q := homTensorCurrySectionMap R (K.X i) (L.X j) ≫
    (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) i j p hij).val
  change ((a.val.app (op W.unop.left)).hom s).app (op (Over.mk (𝟙 W.unop.left)))
      (T.val.map W.unop.hom.op ((q.app U).hom (x ⊗ₜ[R.obj.obj U] y))) =
    ((b.val.app (op W.unop.left)).hom s).app (op (Over.mk (𝟙 W.unop.left)))
      (T.val.map W.unop.hom.op ((q.app U).hom (x ⊗ₜ[R.obj.obj U] y)))
  have hq := (PresheafOfModules.naturality_apply q W.unop.hom.op
    (x ⊗ₜ[R.obj.obj U] y)).symm
  have ha := congrArg
    (((a.val.app (op W.unop.left)).hom s).app (op (Over.mk (𝟙 W.unop.left)))).hom hq
  have hb := congrArg
    (((b.val.app (op W.unop.left)).hom s).app (op (Over.mk (𝟙 W.unop.left)))).hom hq
  exact ha.trans ((h (op W.unop.left) s (op (Over.mk (𝟙 W.unop.left))) i j hij
    ((K.X i).val.map W.unop.hom.op x) ((L.X j).val.map W.unop.hom.op y)).trans hb.symm)


set_option backward.isDefEq.respectTransparency true in
set_option synthInstance.maxSize 256 in
/-- There is one reverse map inverse to every forward map with the currying equation.
Source: Stacks Project, Tag 0A90, inverse construction 
(blueprint: lem-sc-hom-tensor-degreewise-iso).

Proof: Restrict a localized map from each total-degree coproduct to its summands.
Apply the localized tensor-Hom adjunction to curry the K and L inputs successively.
Combine the q components by the inner Hom product universal property and then the
p components by the outer Hom product universal property. Restriction naturality
of currying gives a sheaf morphism in the reverse direction. To check the first
composite, project to p and q and evaluate at x and y; the assumed equation and
the tensor-Hom inverse laws give the identity. For the second composite, project
to total degree, restrict to a summand, and check on pure tensors before
sheafification; the same inverse laws give the identity. Product and coproduct
extensionality, and the sheafification adjunction, establish the two identities,
so the original morphism is an isomorphism. The reverse map is constructed
independently of a forward map;
the inverse calculations apply to every map satisfying the evaluation equation. -/
theorem homTensorDegreewise_inverse (K L M : CochainComplex Mod ℤ) (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ∃ b : (homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).X n ⟶
      (homComplex (R := R) K (homComplex (R := R) L M)).X n,
      ∀ a, HomTensorDegreewiseEquation R K L M n a → a ≫ b = 𝟙 _ ∧ b ≫ a = 𝟙 _ := by
  let := SheafOfModules.monoidalCategory R
  obtain ⟨b, hb⟩ := homTensorDegreewise_reverse_construct R K L M n
  refine ⟨b, ?_⟩
  intro a ha
  unfold HomTensorDegreewiseEquation at ha
  constructor
  · apply homTerm_hom_ext R K (homComplex (R := R) L M) n
    intro p
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply homTerm_section_ext' R L M (p + n) (op W.unop.left)
    intro q t hqt
    have ht : t = p + q + n := by omega
    subst ht
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    let π := homTensorCurryProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl
    let ψ₁ := (((a ≫ b) ≫ π).val.app U).hom s
    let ψ₂ := ((𝟙 _ ≫ π).val.app U).hom s
    let ρ := homTensorCurryProjection R L M (p + n) q (p + q + n) (by omega)
    change (((ρ.val.app (op W.unop.left)).hom ((ψ₁.app W).hom x)).app V).hom y =
      (((ρ.val.app (op W.unop.left)).hom ((ψ₂.app W).hom x)).app V).hom y
    rw [hom_eval_restrict R ρ (op W.unop.left) ((ψ₁.app W).hom x) V y,
      hom_eval_restrict R ρ (op W.unop.left) ((ψ₂.app W).hom x) V y]
    let W' : (Over U.unop)ᵒᵖ := op (Over.mk (V.unop.hom ≫ W.unop.hom))
    let f : W ⟶ W' := (Over.homMk V.unop.hom rfl).op
    have h₁ := PresheafOfModules.naturality_apply ψ₁ f x
    have h₂ := PresheafOfModules.naturality_apply ψ₂ f x
    change (ψ₁.app W').hom ((K.X p).val.map V.unop.hom.op x) =
      ((homComplex (R := R) L M).X (p + n)).val.map V.unop.hom.op
        ((ψ₁.app W).hom x) at h₁
    change (ψ₂.app W').hom ((K.X p).val.map V.unop.hom.op x) =
      ((homComplex (R := R) L M).X (p + n)).val.map V.unop.hom.op
        ((ψ₂.app W).hom x) at h₂
    rw [← h₁, ← h₂]
    exact (hb p q U ((a.val.app U).hom s) W'
      ((K.X p).val.map V.unop.hom.op x) y).symm.trans
        (ha p q U s W' ((K.X p).val.map V.unop.hom.op x) y)
  · apply homTerm_hom_ext R
      (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M n
    intro t
    apply tensorLocalized_ext R K L (M.X (t + n)) _ t
    intro U s W p q hpq x y
    subst t
    exact (ha p q U ((b.val.app U).hom s) W x y).trans (hb p q U s W x y).symm

end CategoryTheory
