/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomTensorSectionNaturality

/-!
# Localized pure-tensor differential calculation

Source: Stacks Project, Tag 0A90 and the calculation in Tag 0A5Y.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

private lemma map_units {A B F : Type*} [AddCommGroup A] [AddCommGroup B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F) (e : ℤˣ) (x : A) :
    f (e • x) = e • f x := by
  exact map_zsmul f (e : ℤ) x

private lemma map_sub_units {A B F : Type*} [AddCommGroup A] [AddCommGroup B]
    [FunLike F A B] [AddMonoidHomClass F A B] (f : F) (e : ℤˣ) (x y : A) :
    f (x - e • y) = f x - e • f y := by
  rw [map_sub, map_units]

private lemma sub_negOnePow_swap {A : Type*} [AddCommGroup A]
    (n p : ℤ) (x y z : A) :
    x - (p + n).negOnePow • z - n.negOnePow • y =
      x - n.negOnePow • y - n.negOnePow • (p.negOnePow • z) := by
  rw [Int.negOnePow_add, mul_comm p.negOnePow n.negOnePow, mul_smul]
  exact sub_right_comm _ _ _

private lemma composite_hom_eval {A A' B B' D E : Mod}
    (a : D ⟶ E) (b : E ⟶ SheafOfModules.homObj (R := R) A B)
    (f : A' ⟶ A) (g : B ⟶ B') (U : Cᵒᵖ) (s : D.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A'.val.obj (op W.unop.left)) :
    ((((a ≫ b ≫ SheafOfModules.homObjMap (R := R) f g).val.app U).hom s).app W).hom x =
      (g.val.app (op W.unop.left)).hom
        (((((b.val.app U).hom ((a.val.app U).hom s)).app W).hom
          ((f.val.app (op W.unop.left)).hom x))) := by
  rfl

private lemma section_sub_units {A B : Mod} (f g : A ⟶ B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : A.val.obj U) :
    ((f - e • g).val.app U).hom s =
      (f.val.app U).hom s - e • (g.val.app U).hom s := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj U
  change (V.map (f - e • g)).hom s = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private lemma section_units {A B : Mod} (f : A ⟶ B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : A.val.obj U) :
    ((e • f).val.app U).hom s = e • (f.val.app U).hom s := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let V := SheafOfModules.forget R₀ ⋙ PresheafOfModules.evaluation R₀.obj U
  change (V.map (e • f)).hom s = _
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma hom_section_sub_units {A B D : Mod}
    (f g : D ⟶ SheafOfModules.homObj (R := R) A B)
    (e : ℤˣ) (U : Cᵒᵖ) (s : D.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj (op W.unop.left)) :
    ((((f - e • g).val.app U).hom s).app W).hom x =
      (((f.val.app U).hom s).app W).hom x -
        e • (((g.val.app U).hom s).app W).hom x := by
  rw [section_sub_units]
  change (((((f.val.app U).hom s - (e : ℤ) • (g.val.app U).hom s) :
    (PresheafOfModules.restrictOver R.obj U.unop).obj A.val ⟶
      (PresheafOfModules.restrictOver R.obj U.unop).obj B.val).app W).hom x) = _
  erw [PresheafOfModules.sub_app, PresheafOfModules.zsmul_app,
    ModuleCat.hom_sub, ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private noncomputable def localizedEval {A B : Mod} (U : Cᵒᵖ)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj (op W.unop.left)) :
    (SheafOfModules.homObj (R := R) A B).val.obj U →+
      B.val.obj (op W.unop.left) where
  toFun s := (s.app W).hom x
  map_zero' := rfl
  map_add' _s _t := rfl

set_option backward.isDefEq.respectTransparency true in
private theorem differential_projection (A B : CochainComplex Mod ℤ)
    (n p q q' p' : ℤ) (hpq : p + (n + 1) = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    (homComplex (R := R) A B).d n (n + 1) ≫
      homTensorProjection R A B (n + 1) p q hpq =
    homTensorProjection R A B n p q' hq' ≫
      SheafOfModules.homObjMap (R := R) (𝟙 (A.X p)) (B.d q' q) -
    n.negOnePow • (homTensorProjection R A B n p' q hp' ≫
      SheafOfModules.homObjMap (R := R) (A.d p p') (𝟙 (B.X q))) := by
  exact (Classical.choose_spec
    (homComplex_projections_exists (R := R))).2.1 A B n (n + 1) p q q' p'
      rfl hpq hq' hp'

-- Keep the chosen bifunctor abstract after exposing its differential formula.
attribute [local irreducible] homComplexFunctor

set_option backward.isDefEq.respectTransparency false in
private theorem differential_apply (A B : CochainComplex Mod ℤ)
    (n p q q' p' : ℤ) (hpq : p + (n + 1) = q)
    (hq' : p + n = q') (hp' : p' + n = q)
    (U : Cᵒᵖ) (s : (homComplex (R := R) A B).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (A.X p).val.obj (op W.unop.left)) :
    (((((homTensorProjection R A B (n + 1) p q hpq).val.app U).hom
      ((((homComplex (R := R) A B).d n (n + 1)).val.app U).hom s)).app W).hom x) =
    ((B.d q' q).val.app (op W.unop.left)).hom
      (((((homTensorProjection R A B n p q' hq').val.app U).hom s).app W).hom x) -
    n.negOnePow • (show (B.X q).val.obj (op W.unop.left) from
      (((((homTensorProjection R A B n p' q hp').val.app U).hom s).app W).hom
        (((A.d p p').val.app (op W.unop.left)).hom x))) := by
  have he := congrArg (fun f ↦ (((f.val.app U).hom s).app W).hom x)
    (differential_projection R A B n p q q' p' hpq hq' hp')
  rw [hom_section_sub_units] at he
  exact he

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_pure_map {A A' B B' : Mod}
    (f : A' ⟶ A) (g : B' ⟶ B) (V : Cᵒᵖ)
    (x : A'.val.obj V) (y : B'.val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    ((f ⊗ₘ g).val.app V).hom
      (((homTensorSectionMap R A' B').app V).hom (x ⊗ₜ[R.obj.obj V] y)) =
    ((homTensorSectionMap R A B).app V).hom
      (((f.val.app V).hom x) ⊗ₜ[R.obj.obj V] ((g.val.app V).hom y)) := by
  let := SheafOfModules.monoidalCategory R
  have he := congrArg (fun t ↦ (t.app V).hom (x ⊗ₜ[R.obj.obj V] y))
    (homTensorSectionMap_natural R f g)
  change _ = ((homTensorSectionMap R A B).app V).hom
    (((f.val ⊗ₘ g.val).app V).hom (x ⊗ₜ[R.obj.obj V] y)) at he
  erw [PresheafOfModules.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  exact he

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_d₁ (K L : CochainComplex Mod ℤ) (p q : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod) (.up ℤ) p q (p + q + 1) =
      (K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
        CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          (p + 1) q (p + q + 1) (by omega) := by
  let := SheafOfModules.monoidalCategory R
  rw [HomologicalComplex.mapBifunctor.d₁_eq K L (curriedTensor Mod) (.up ℤ)
    (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q (p + q + 1) (by dsimp; omega)]
  change (1 : ℤˣ) • _ = _
  rw [one_smul]
  simp

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_d₂ (K L : CochainComplex Mod ℤ) (p q : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod) (.up ℤ) p q (p + q + 1) =
      p.negOnePow • ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
        CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
          p (q + 1) (p + q + 1) (by omega)) := by
  let := SheafOfModules.monoidalCategory R
  rw [HomologicalComplex.mapBifunctor.d₂_eq K L (curriedTensor Mod) (.up ℤ)
    p (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) (p + q + 1) (by dsimp; omega)]
  change p.negOnePow • _ = _
  congr 1
  simp

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_d₁_pure (K L : CochainComplex Mod ℤ) (p q : ℤ) (V : Cᵒᵖ)
    (x : (K.X p).val.obj V) (y : (L.X q).val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    ((HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)).val.app V).hom
      (((homTensorSectionMap R (K.X p) (L.X q)).app V).hom (x ⊗ₜ[R.obj.obj V] y)) =
    ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
      (p + 1) q (p + q + 1) (by omega)).val.app V).hom
      (((homTensorSectionMap R (K.X (p + 1)) (L.X q)).app V).hom
        ((((K.d p (p + 1)).val.app V).hom x) ⊗ₜ[R.obj.obj V] y)) := by
  let := SheafOfModules.monoidalCategory R
  rw [tensor_d₁]
  have he := tensor_pure_map R (K.d p (p + 1)) (𝟙 (L.X q)) V x y
  exact congrArg ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
    (p + 1) q (p + q + 1) (by omega)).val.app V).hom he

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem tensor_d₂_pure (K L : CochainComplex Mod ℤ) (p q : ℤ) (V : Cᵒᵖ)
    (x : (K.X p).val.obj V) (y : (L.X q).val.obj V) :
    letI := SheafOfModules.monoidalCategory R
    ((HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)).val.app V).hom
      (((homTensorSectionMap R (K.X p) (L.X q)).app V).hom (x ⊗ₜ[R.obj.obj V] y)) =
    p.negOnePow • ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
      p (q + 1) (p + q + 1) (by omega)).val.app V).hom
      (((homTensorSectionMap R (K.X p) (L.X (q + 1))).app V).hom
        (x ⊗ₜ[R.obj.obj V] (((L.d q (q + 1)).val.app V).hom y))) := by
  let := SheafOfModules.monoidalCategory R
  rw [tensor_d₂, section_units]
  have he := tensor_pure_map R (𝟙 (K.X p)) (L.d q (q + 1)) V x y
  exact congrArg (fun z ↦ p.negOnePow •
    ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
      p (q + 1) (p + q + 1) (by omega)).val.app V).hom z) he

set_option synthInstance.maxSize 256 in
set_option backward.isDefEq.respectTransparency true in
private theorem curry_apply (K L M : CochainComplex Mod ℤ)
    (n p q t m r : ℤ) (h : p + q = t) (hm : t + n = m) (hr : p + n = r)
    (U : Cᵒᵖ)
    (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
    (y : (L.X q).val.obj (op W.unop.left)) :
    letI := SheafOfModules.monoidalCategory R
    let φ := ((homTensorProjection R (CochainComplex.mapBifunctor K L (curriedTensor Mod))
      M n t m hm).val.app U).hom ((homTensorDegreewiseMap R K L M n).val.app U |>.hom s)
    let ψ := ((homTensorProjection R K (homComplex (R := R) L M)
      n p r hr).val.app U).hom s
    let χ := ((homTensorProjection R L M r q m (by omega)).val.app
      (op W.unop.left)).hom ((ψ.app W).hom x)
    (φ.app W).hom
      (((CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h).val.app
        (op W.unop.left)).hom
          (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
            (x ⊗ₜ[R.obj.obj (op W.unop.left)] y))) =
      (χ.app (op (Over.mk (𝟙 W.unop.left)))).hom y := by
  subst r t m
  exact (homTensorDegreewiseMap_spec R K L M n).1 p q U s W x y

set_option synthInstance.maxSize 256 in
/-- The iterated Hom differential agrees with the three tensor differential terms
on one localized pure tensor.
Source: Stacks Project, Tag 0A90 and the calculation in More on Algebra Tag 0A5Y.
(blueprint: lem-sc-hom-tensor-differential-summand-pure)

Proof: Apply the degree-(n+1) curry equation to the image of s under the outer
Hom differential. Expand that differential using its product projection identity.
Its postcomposition evaluates the inner differential on the outer evaluation of s;
its precomposition contributes minus (-1)^n times the evaluation at d_K(x).
Expand the inner differential: its postcomposition is d_M applied to f(x)(y),
and its precomposition is minus (-1)^(p+n) times f(x)(d_L(y)).
Apply the degree-n curry equation separately to the three terms on the right.
The first tensor summand differential sends x tensor y to d_K(x) tensor y.
The second sends it to (-1)^p times x tensor d_L(y), by the definition of d2.
Naturality of the canonical presheaf-to-sheaf tensor map identifies these values
before and after sheafification. The sign identity (p+n).negOnePow =
p.negOnePow * n.negOnePow then identifies the second inner differential term
with the signed d2 term. The two subtractions occur in opposite order, which
commute in the target module. The argument works for all integer degrees and
zero sections, tensor factors or differentials. This is only a scalar equality
on pure tensors and does not assert extensionality on sheaf tensors. -/
theorem homTensorDifferential_summand_pure
    (K L M : CochainComplex Mod ℤ) (n t p q : ℤ) (h : p + q = t) :
    letI := SheafOfModules.monoidalCategory R
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    let ι := CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q t h
    let f :=
      (homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl ≫
            SheafOfModules.homObjMap (R := R) ι (𝟙 (M.X (t + (n + 1))))
    let g :=
      (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n t (t + n) rfl ≫
          SheafOfModules.homObjMap (R := R) ι (M.d (t + n) (t + (n + 1)))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1))))) -
      n.negOnePow • (homTensorDegreewiseMap R K L M n ≫
        homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod)
              (ComplexShape.up ℤ) p q (t + 1)) (𝟙 (M.X (t + (n + 1)))))
    ∀ (U : Cᵒᵖ)
      (s : (homComplex (R := R) K (homComplex (R := R) L M)).X n |>.val.obj U)
      (W : (Over U.unop)ᵒᵖ) (x : (K.X p).val.obj (op W.unop.left))
      (y : (L.X q).val.obj (op W.unop.left)),
      (((f.val.app U).hom s).app W).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) =
      (((g.val.app U).hom s).app W).hom
        (((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
          (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)) := by
  let := SheafOfModules.monoidalCategory R
  subst t
  dsimp only
  intro U s W x y
  have hc := curry_apply R K L M (n + 1) p q (p + q) (p + q + (n + 1))
    (p + n + 1) rfl rfl (by omega)
    U ((((homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1)).val.app U).hom s)
    W x y
  have ho := differential_apply R K (homComplex (R := R) L M) n p
    (p + n + 1) (p + n) (p + 1) (by omega) rfl (by omega) U s W x
  have hi := differential_apply R L M (p + n) q (p + q + (n + 1))
    (p + q + n) (q + 1) (by omega) (by omega) (by omega) (op W.unop.left)
    (((((homTensorProjection R K (homComplex (R := R) L M)
      n p (p + n) rfl).val.app U).hom s).app W).hom x)
    (op (Over.mk (𝟙 W.unop.left))) y
  let E : ((homComplex (R := R) L M).X (p + n + 1)).val.obj (op W.unop.left) →+
      (M.X (p + q + (n + 1))).val.obj (op W.unop.left) :=
    (localizedEval R (op W.unop.left) (op (Over.mk (𝟙 W.unop.left))) y).comp
      (((homTensorProjection R L M (p + n + 1) q (p + q + (n + 1))
        (by omega)).val.app (op W.unop.left)).hom.toAddMonoidHom)
  have hx := (congrArg E ho).trans (map_sub_units E n.negOnePow _ _)
  let w1 : ((homComplex (R := R) L M).X (p + n + 1)).val.obj (op W.unop.left) :=
    (((((homTensorProjection R K (homComplex (R := R) L M)
      n (p + 1) (p + n + 1) (by omega)).val.app U).hom s).app W).hom
        (((K.d p (p + 1)).val.app (op W.unop.left)).hom x))
  have hl := (hc.trans hx).trans (congrArg
    (fun v : (M.X (p + q + (n + 1))).val.obj (op W.unop.left) ↦
      v - n.negOnePow • E w1) hi)
  have h0 := curry_apply R K L M n p q (p + q) (p + q + n) (p + n) rfl rfl rfl
    U s W x y
  have h1 := curry_apply R K L M n (p + 1) q (p + q + 1) (p + q + (n + 1))
    (p + n + 1) (by omega) (by omega) (by omega)
    U s W (((K.d p (p + 1)).val.app (op W.unop.left)).hom x) y
  have h2 := curry_apply R K L M n p (q + 1) (p + q + 1) (p + q + (n + 1))
    (p + n) (by omega) (by omega) rfl
    U s W x (((L.d q (q + 1)).val.app (op W.unop.left)).hom y)
  have hd1 := tensor_d₁_pure R K L p q (op W.unop.left) x y
  have hd2 := tensor_d₂_pure R K L p q (op W.unop.left) x y
  let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
  let a := homTensorDegreewiseMap R K L M n
  let π0 := homTensorProjection R T M n (p + q) (p + q + n) rfl
  let π1 := homTensorProjection R T M n (p + q + 1) (p + q + (n + 1)) (by omega)
  let z := ((homTensorSectionMap R (K.X p) (L.X q)).app (op W.unop.left)).hom
    (x ⊗ₜ[R.obj.obj (op W.unop.left)] y)
  have he0 := composite_hom_eval R a π0
    (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q (p + q) rfl)
    (M.d (p + q + n) (p + q + (n + 1))) U s W z
  have he1 := composite_hom_eval R a π1
    (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1)))) U s W z
  have he2 := composite_hom_eval R a π1
    (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1)))) U s W z
  let F0 := a ≫ π0 ≫ SheafOfModules.homObjMap (R := R)
    (CochainComplex.ιMapBifunctor K L (curriedTensor Mod) p q (p + q) rfl)
    (M.d (p + q + n) (p + q + (n + 1)))
  let F1 := a ≫ π1 ≫ SheafOfModules.homObjMap (R := R)
    (HomologicalComplex.mapBifunctor.d₁ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1))))
  let F2 := a ≫ π1 ≫ SheafOfModules.homObjMap (R := R)
    (HomologicalComplex.mapBifunctor.d₂ K L (curriedTensor Mod) (.up ℤ)
      p q (p + q + 1)) (𝟙 (M.X (p + q + (n + 1))))
  let e : ((homComplex (R := R) K (homComplex (R := R) L M)).X n ⟶
      SheafOfModules.homObj (R := R) (K.X p ⊗ L.X q) (M.X (p + q + (n + 1)))) →
      (M.X (p + q + (n + 1))).val.obj (op W.unop.left) :=
    fun f ↦ (((f.val.app U).hom s).app W).hom z
  have hs0 : e (F0 - n.negOnePow • F1) = e F0 - n.negOnePow • e F1 :=
    hom_section_sub_units R F0 F1 n.negOnePow U s W z
  have hs1 : e (F0 - n.negOnePow • F1 - n.negOnePow • F2) =
      e (F0 - n.negOnePow • F1) - n.negOnePow • e F2 :=
    hom_section_sub_units R (F0 - n.negOnePow • F1) F2 n.negOnePow U s W z
  let φ1 := (π1.val.app U).hom ((a.val.app U).hom s)
  let ev1 : (T.X (p + q + 1)).val.obj (op W.unop.left) →
      (M.X (p + q + (n + 1))).val.obj (op W.unop.left) :=
    fun w ↦ (φ1.app W).hom w
  have hA := he0.trans
    (congrArg ((M.d (p + q + n) (p + q + (n + 1))).val.app (op W.unop.left)).hom h0)
  have hB := he1.trans ((congrArg ev1 hd1).trans h1)
  let z2 := ((CochainComplex.ιMapBifunctor K L (curriedTensor Mod)
    p (q + 1) (p + q + 1) (by omega)).val.app (op W.unop.left)).hom
      (((homTensorSectionMap R (K.X p) (L.X (q + 1))).app (op W.unop.left)).hom
        (x ⊗ₜ[R.obj.obj (op W.unop.left)]
          (((L.d q (q + 1)).val.app (op W.unop.left)).hom y)))
  have hC := he2.trans ((congrArg ev1 hd2).trans
    ((map_units (φ1.app W).hom p.negOnePow z2).trans
      (congrArg (fun v : (M.X (p + q + (n + 1))).val.obj (op W.unop.left) ↦
        p.negOnePow • v) h2)))
  have hr := hs1.trans (congrArg
    (fun v : (M.X (p + q + (n + 1))).val.obj (op W.unop.left) ↦
      v - n.negOnePow • e F2) hs0)
  have hr' := hr.trans
    (congrArg₂ (fun v w : (M.X (p + q + (n + 1))).val.obj (op W.unop.left) ↦
      v - n.negOnePow • w)
      (congrArg₂ (fun v w : (M.X (p + q + (n + 1))).val.obj (op W.unop.left) ↦
        v - n.negOnePow • w) hA hB) hC)
  exact hl.trans ((sub_negOnePow_swap n p _ _ _).trans hr'.symm)

end CategoryTheory
