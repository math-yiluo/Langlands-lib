/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorHorizontalSections
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-! # Horizontal compatibility of the ordinary geometric tensor comparison

Source: Zheng Construction 4.1; Stacks 03EL.
(blueprint: lem-coef-geometric-tensor-component-horizontal)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] evaluation transition tensorSection ordinaryEvaluationTensor
attribute [local irreducible] coefficientMap systemRing evalSection rings ringPresheaf
attribute [local irreducible] Functor.ofSequence Functor.ofOpSequence Prod.sectR
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] SheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
attribute [local implicit_reducible] PresheafOfModules.restrictScalarsObj
attribute [local implicit_reducible] PresheafOfModules.presheaf ModuleCat.restrictScalars
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

private def horizontalUnderlying {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) :
    (underlying.{c, v, r} J (B m)).obj
        ((evaluation.{c, v, max c v r} J B τ m).obj M) ⟶
      (underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj M) :=
  (underlying.{c, v, r} J (B m)).map
    ((transition.{c, v, max c v r} J B τ h).app M)

private def imageIdentification (n : ℕ) (M : Systems.{c, v, max c v r} J B τ) :
    (underlying.{c, v, r} J' (O.coefficients n)).obj
        ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
          (O.pull.obj M)) ≅
      uInv.obj ((underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj M)) :=
  (underlying.{c, v, r} J' (O.coefficients n)).mapIso
      ((O.ordinaryPullEvaluation n).app M) ≪≫
    (O.inverseImage n).moduleUnderlying.app _

private theorem horizontal_normalization {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) :
    horizontalUnderlying.{c, v, r} J' O.coefficients O.coefficientTransition h (O.pull.obj M) ≫
        (imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O n M).hom =
      (imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O m M).hom ≫
        uInv.map (horizontalUnderlying.{c, v, r} J B τ h M) := by
  let F := underlying.{c, v, r} J' (O.coefficients m)
  let t := (transition.{c, v, max c v r} J' O.coefficients O.coefficientTransition h).app
    (O.pull.obj M)
  let e := (O.ordinaryPullEvaluation n).hom.app M
  let d := (transition.{c, v, max c v r} J B τ h).app M
  let b := (O.restrictionPullback h).hom.app
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
  calc
    _ = F.map (t ≫ (res (coefficientMap J' O.coefficients
        O.coefficientTransition h)).map e) ≫
        (O.inverseImage n).moduleUnderlying.hom.app _ := by
      simp only [Functor.map_comp, Category.assoc]
      rfl
    _ = F.map ((O.ordinaryPullEvaluation m).hom.app M ≫
        (O.inverseImage m).modules.map d ≫ b) ≫
        (O.inverseImage n).moduleUnderlying.hom.app _ :=
      congrArg (fun k ↦ F.map k ≫ (O.inverseImage n).moduleUnderlying.hom.app _)
        (O.ordinaryPullTransition h M)
    _ = F.map ((O.ordinaryPullEvaluation m).hom.app M) ≫
        F.map ((O.inverseImage m).modules.map d) ≫
          (F.map b ≫ (O.inverseImage n).moduleUnderlying.hom.app _) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map ((O.ordinaryPullEvaluation m).hom.app M) ≫
        F.map ((O.inverseImage m).modules.map d) ≫
          (O.inverseImage m).moduleUnderlying.hom.app _ :=
      congrArg (fun k ↦ F.map ((O.ordinaryPullEvaluation m).hom.app M) ≫
        F.map ((O.inverseImage m).modules.map d) ≫ k)
          (O.restrictionPullback_underlying h _)
    _ = _ := by
      have hn := (O.inverseImage m).moduleUnderlying.hom.naturality d
      exact congrArg (fun k ↦ F.map ((O.ordinaryPullEvaluation m).hom.app M) ≫ k) hn

private def imageMap (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    {Z : Sheaf J (Type (max c v r))}
    (x : Z ⟶ (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj M)) :
    uInv.obj Z ⟶ (underlying.{c, v, r} J' (O.coefficients n)).obj
      ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
        (O.pull.obj M)) :=
  uInv.map x ≫ (imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O n M).inv

private theorem imageMap_transition {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) {Z : Sheaf J (Type (max c v r))}
    (x : Z ⟶ (underlying.{c, v, r} J (B m)).obj
      ((evaluation.{c, v, max c v r} J B τ m).obj M)) :
    imageMap.{c, v, r} J B τ J' uInv uPush adjSet O m M x ≫
        horizontalUnderlying.{c, v, r} J' O.coefficients O.coefficientTransition h (O.pull.obj M) =
      imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n M
        (x ≫ horizontalUnderlying.{c, v, r} J B τ h M) := by
  apply (cancel_mono (imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O n M).hom).mp
  dsimp only [imageMap]
  simp only [Category.assoc, horizontal_normalization.{c, v, r} J B τ J' uInv uPush adjSet O,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp]

variable (μ : ∀ (n : ℕ) (M N : Mod.{c, v, max c v r} J (B n)),
  (O.inverseImage n).modules.obj (ordinaryTensor.{c, v, r} J (B n) M N) ≅
    ordinaryTensor.{c, v, r} J' (O.coefficients n)
      ((O.inverseImage n).modules.obj M) ((O.inverseImage n).modules.obj N))

/-- The forced component of the system tensor comparison.
Source: Zheng Construction 4.1; Stacks 03EL.
(blueprint: lem-coef-geometric-tensor-component-horizontal). -/
@[irreducible] def geometricTensorComponent (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
        (O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N)) ≅
      (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
          (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
          (O.pull.obj M) (O.pull.obj N)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  exact (O.ordinaryPullEvaluation n).app _ ≪≫
    (O.inverseImage n).modules.mapIso (ordinaryEvaluationTensor.{c, v, r} J B τ n M N) ≪≫
    μ n ((evaluation.{c, v, max c v r} J B τ n).obj M)
      ((evaluation.{c, v, max c v r} J B τ n).obj N) ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      ((O.ordinaryPullEvaluation n).app M).symm
      ((O.ordinaryPullEvaluation n).app N).symm ≪≫
    (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
      (O.pull.obj M) (O.pull.obj N)).symm

private theorem iso_hom_inv_section
    {R : Sheaf J' CommRingCat.{max c v r}}
    {M N : Mod.{c, v, max c v r} J' R} (e : M ≅ N)
    (V : C'ᵒᵖ) (x : N.val.obj V) :
    e.hom.val.app V (e.inv.val.app V x) = x :=
  congrArg (fun f ↦ f.val.app V x) e.inv_hom_id

private theorem tensor_transition_inv_pure {m n : ℕ} (h : n ≤ m)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J B τ m).obj M).val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ m).obj N).val.obj U) :
    ((transition.{c, v, max c v r} J B τ h).app _).val.app U
        ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
          (tensorSection.{c, v, r} J (B m) _ _ U x y)) =
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U
        (tensorSection.{c, v, r} J (B n) _ _ U
          (((transition.{c, v, max c v r} J B τ h).app M).val.app U x)
          (((transition.{c, v, max c v r} J B τ h).app N).val.app U y)) := by
  have ht := congrArg ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U)
    (evaluation_tensor_transition_pure.{c, v, r} J B τ h M N U x y)
  have hi := congrArg (fun k ↦ k.val.app U
    (((transition.{c, v, max c v r} J B τ h).app _).val.app U
      ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
        (tensorSection.{c, v, r} J (B m) _ _ U x y))))
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom_inv_id
  exact hi.symm.trans ht

private theorem inverse_map_section (n : ℕ)
    {M N : Mod.{c, v, max c v r} J (B n)} (f : M ⟶ N)
    {Z : Sheaf J (Type (max c v r))}
    (x : Z ⟶ (underlying.{c, v, r} J (B n)).obj M)
    (V : C'ᵒᵖ) (a : (uInv.obj Z).obj.obj V) :
    ((O.inverseImage n).modules.map f).val.app V
        (((O.inverseImage n).moduleUnderlying.inv.app M).hom.app V
          ((uInv.map x).hom.app V a)) =
      ((O.inverseImage n).moduleUnderlying.inv.app N).hom.app V
        ((uInv.map (x ≫ (underlying.{c, v, r} J (B n)).map f)).hom.app V a) := by
  rw [Functor.map_comp]
  exact congrArg (fun k ↦ k.hom.app V ((uInv.map x).hom.app V a))
    ((O.inverseImage n).moduleUnderlying.inv.naturality f).symm

private theorem component_pure
    (hp : ∀ n : ℕ, InverseTensorPure.{c, v, r} J J' uInv
      (B n) (O.coefficients n) (O.inverseImage n) (μ n))
    (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    (Z : Sheaf J (Type (max c v r)))
    (x : Z ⟶ (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj M))
    (y : Z ⟶ (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj N))
    (z : Z ⟶ (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) M N)))
    (hz : ∀ (U : Cᵒᵖ) (a : Z.obj.obj U),
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
          (z.hom.app U a) =
        tensorSection.{c, v, r} J (B n) _ _ U (x.hom.app U a) (y.hom.app U a))
    (V : C'ᵒᵖ) (a : (uInv.obj Z).obj.obj V) :
    (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N).hom.val.app V
        ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n _ z).hom.app V a) =
      (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
        (O.pull.obj M) (O.pull.obj N)).inv.val.app V
        (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V
          ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n M x).hom.app V a)
          ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n N y).hom.app V a)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  unfold geometricTensorComponent
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, MonoidalCategory.tensorIso_hom, imageMap, imageIdentification,
    Iso.trans_inv, Functor.mapIso_inv]
  change (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
      (O.pull.obj M) (O.pull.obj N)).inv.val.app V
    ((ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
      ((O.ordinaryPullEvaluation n).inv.app M)
      ((O.ordinaryPullEvaluation n).inv.app N)).val.app V
      ((μ n _ _).hom.val.app V
        (((O.inverseImage n).modules.map
          (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom).val.app V
          (((O.ordinaryPullEvaluation n).hom.app _).val.app V
            (((O.ordinaryPullEvaluation n).inv.app _).val.app V
              (((O.inverseImage n).moduleUnderlying.inv.app _).hom.app V
                ((uInv.map z).hom.app V a))))))) = _
  erw [iso_hom_inv_section.{c, v, r} J' ((O.ordinaryPullEvaluation n).app _) V _,
    inverse_map_section.{c, v, r} J B τ J' uInv uPush adjSet O,
    hp n _ _ Z x y _ hz V a, tensorSection_map.{c, v, r} J']
  rfl

private def purePair (R : Sheaf J CommRingCat.{max c v r})
    (M N : Mod.{c, v, max c v r} J R) :
    (underlying.{c, v, r} J R).obj M ⊗ (underlying.{c, v, r} J R).obj N ⟶
      (underlying.{c, v, r} J R).obj (ordinaryTensor.{c, v, r} J R M N) :=
  ⟨{ app := fun U ↦ ↾(fun p ↦ tensorSection.{c, v, r} J R M N U p.1 p.2)
     naturality := by
       intro U V f
       ext p
       exact (tensorSection_restrict.{c, v, r} J M N f p.1 p.2).symm }⟩

private theorem imageMap_pair_sections [PreservesFiniteLimits uInv]
    (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) (V : C'ᵒᵖ)
    (x : ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
      (O.pull.obj M)).val.obj V)
    (y : ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
      (O.pull.obj N)).val.obj V) :
    ∃ a : (uInv.obj
      ((underlying.{c, v, r} J (B n)).obj
          ((evaluation.{c, v, max c v r} J B τ n).obj M) ⊗
        (underlying.{c, v, r} J (B n)).obj
          ((evaluation.{c, v, max c v r} J B τ n).obj N))).obj.obj V,
      (imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n M
        (CartesianMonoidalCategory.fst _ _)).hom.app V a = x ∧
      (imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n N
        (CartesianMonoidalCategory.snd _ _)).hom.app V a = y := by
  let : uInv.Braided := Functor.Braided.ofChosenFiniteProducts uInv
  let eM := imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O n M
  let eN := imageIdentification.{c, v, r} J B τ J' uInv uPush adjSet O n N
  let a := (Functor.LaxMonoidal.μ uInv _ _).hom.app V
    (eM.hom.hom.app V x, eN.hom.hom.app V y)
  refine ⟨a, ?_, ?_⟩
  · have h := congrArg (fun k ↦ k.hom.app V
      (eM.hom.hom.app V x, eN.hom.hom.app V y)) (Functor.Monoidal.μ_fst uInv _ _)
    change (uInv.map (CartesianMonoidalCategory.fst _ _)).hom.app V a =
      eM.hom.hom.app V x at h
    change eM.inv.hom.app V
      ((uInv.map (CartesianMonoidalCategory.fst _ _)).hom.app V a) = x
    rw [h]
    exact congrArg (fun k ↦ k.hom.app V x) eM.hom_inv_id
  · have h := congrArg (fun k ↦ k.hom.app V
      (eM.hom.hom.app V x, eN.hom.hom.app V y)) (Functor.Monoidal.μ_snd uInv _ _)
    change (uInv.map (CartesianMonoidalCategory.snd _ _)).hom.app V a =
      eN.hom.hom.app V y at h
    change eN.inv.hom.app V
      ((uInv.map (CartesianMonoidalCategory.snd _ _)).hom.app V a) = y
    rw [h]
    exact congrArg (fun k ↦ k.hom.app V y) eN.hom_inv_id

private theorem component_hom_ext [PreservesFiniteLimits uInv]
    (hp : ∀ n : ℕ, InverseTensorPure.{c, v, r} J J' uInv
      (B n) (O.coefficients n) (O.inverseImage n) (μ n))
    (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    {P : Mod.{c, v, max c v r} J' (O.coefficients n)}
    {f g : (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
      (O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing J B τ) M N)) ⟶ P}
    (hfg : ∀ (Z : Sheaf J (Type (max c v r)))
      (x : Z ⟶ (underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj M))
      (y : Z ⟶ (underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj N))
      (z : Z ⟶ (underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) M N))),
      (∀ (U : Cᵒᵖ) (a : Z.obj.obj U),
        (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
            (z.hom.app U a) =
          tensorSection.{c, v, r} J (B n) _ _ U (x.hom.app U a) (y.hom.app U a)) →
      ∀ (V : C'ᵒᵖ) (a : (uInv.obj Z).obj.obj V),
        f.val.app V ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n _ z).hom.app V a) =
          g.val.app V ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n _ z).hom.app V a)) :
    f = g := by
  let d := geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N
  let b := ordinaryEvaluationTensor.{c, v, r} J' O.coefficients
    O.coefficientTransition n (O.pull.obj M) (O.pull.obj N)
  apply (cancel_epi d.inv).mp
  apply (cancel_epi b.inv).mp
  apply tensor_hom_ext.{c, v, r} J'
  intro V x y
  obtain ⟨a, hx, hy⟩ := imageMap_pair_sections.{c, v, r} J B τ J' uInv uPush adjSet O n M N V x y
  let Z := (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj M) ⊗
    (underlying.{c, v, r} J (B n)).obj
      ((evaluation.{c, v, max c v r} J B τ n).obj N)
  let z : Z ⟶ _ := purePair.{c, v, r} J (B n) _ _ ≫
    (underlying.{c, v, r} J (B n)).map
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv
  have hz (U : Cᵒᵖ) (t : Z.obj.obj U) :
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
        (z.hom.app U t) =
      tensorSection.{c, v, r} J (B n) _ _ U t.1 t.2 := by
    exact iso_hom_inv_section.{c, v, r} J _ U _
  have hd := component_pure.{c, v, r} J B τ J' uInv uPush adjSet O μ hp n M N Z
    (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _) z hz V a
  have hd' := hd.trans (congrArg (b.inv.val.app V)
    (congrArg₂ (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V) hx hy))
  have hi : d.inv.val.app V
      (b.inv.val.app V (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V x y)) =
      (imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n _ z).hom.app V a := by
    exact (congrArg (d.inv.val.app V) hd').symm.trans
      (congrArg (fun k ↦ k.val.app V
        ((imageMap.{c, v, r} J B τ J' uInv uPush adjSet O n _ z).hom.app V a)) d.hom_inv_id)
  change f.val.app V (d.inv.val.app V (b.inv.val.app V _)) =
    g.val.app V (d.inv.val.app V (b.inv.val.app V _))
  exact (congrArg (f.val.app V) hi).trans
    ((hfg Z (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      z hz V a).trans (congrArg (g.val.app V) hi).symm)

/-- The normalized component maps commute with horizontal restriction.
Source: Zheng Construction 4.1 (the actual semilinear transitions); Stacks 03EL
(the bilinear universal property).
(blueprint: lem-coef-geometric-tensor-component-horizontal).

Proof: identify the underlying sheaf of each evaluated pullback using
O.ordinaryPullEvaluation and I.moduleUnderlying. Under these identifications,
O.ordinaryPullTransition and O.restrictionPullback_underlying identify its
horizontal map with inverse image of the original horizontal map. Apply the
pure-tensor equation to the universal pair of generalized sections. Restriction
of scalars changes only the action, so this equation also applies to the
coefficient-restricted horizontal maps; O.coefficient_compatibility supplies the
scalar square. Ordinary tensor evaluation is the identity on pure sections.
Consequently both horizontal composites send the universal pair to the inverse
image of the tensor of its two horizontal restrictions. Balanced tensor
universality and sheafification extend the equality from these pairs to the
whole tensor sheaf. Conjugating back gives the displayed equation of module-sheaf morphisms.
The argument does not assume flatness of any coefficient transition, nor the
existence of points, and also applies to zero modules and empty sites. -/
theorem geometricTensorComponent_horizontal [PreservesFiniteLimits uInv]
    (hp : ∀ n : ℕ, InverseTensorPure.{c, v, r} J J' uInv
      (B n) (O.coefficients n) (O.inverseImage n) (μ n))
    (M N : Systems.{c, v, max c v r} J B τ) :
    ∀ {m n : ℕ} (h : n ≤ m),
      (transition.{c, v, max c v r} J' O.coefficients O.coefficientTransition h).app
          (O.pull.obj (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
            (systemRing.{c, v, max c v r} J B τ) M N)) ≫
        (res.{c, v, max c v r}
          (coefficientMap.{c, v, max c v r} J' O.coefficients O.coefficientTransition h)).map
          (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ n M N).hom =
      (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ m M N).hom ≫
        (transition.{c, v, max c v r} J' O.coefficients O.coefficientTransition h).app
          (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
            (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
            (O.pull.obj M) (O.pull.obj N)) := by
  intro m n h
  apply component_hom_ext.{c, v, r} J B τ J' uInv uPush adjSet O μ hp m M N
  intro Z x y z hz V a
  let T := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) M N
  let xn := x ≫ horizontalUnderlying.{c, v, r} J B τ h M
  let yn := y ≫ horizontalUnderlying.{c, v, r} J B τ h N
  let zn := z ≫ horizontalUnderlying.{c, v, r} J B τ h T
  have hzn (U : Cᵒᵖ) (t : Z.obj.obj U) :
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
          (zn.hom.app U t) =
        tensorSection.{c, v, r} J (B n) _ _ U (xn.hom.app U t) (yn.hom.app U t) := by
    have he : z.hom.app U t =
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
          (tensorSection.{c, v, r} J (B m) _ _ U (x.hom.app U t) (y.hom.app U t)) := by
      exact (congrArg (fun k ↦ k.val.app U (z.hom.app U t))
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom_inv_id).symm.trans
        (congrArg ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U)
          (hz U t))
    change (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      (((transition.{c, v, max c v r} J B τ h).app T).val.app U (z.hom.app U t)) = _
    exact (congrArg (fun q ↦
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
        (((transition.{c, v, max c v r} J B τ h).app T).val.app U q)) he).trans
      (evaluation_tensor_transition_pure.{c, v, r} J B τ h M N U _ _)
  have ht (Q : Systems.{c, v, max c v r} J B τ)
      (q : Z ⟶ (underlying.{c, v, r} J (B m)).obj
        ((evaluation.{c, v, max c v r} J B τ m).obj Q)) :=
    congrArg (fun k ↦ k.hom.app V a)
      (imageMap_transition.{c, v, r} J B τ J' uInv uPush adjSet O h Q q)
  let s (k : ℕ) (Q : Systems.{c, v, max c v r} J B τ)
      (q : Z ⟶ (underlying.{c, v, r} J (B k)).obj
        ((evaluation.{c, v, max c v r} J B τ k).obj Q)) :=
    (imageMap.{c, v, r} J B τ J' uInv uPush adjSet O k Q q).hom.app V a
  let d (k : ℕ) :=
    (geometricTensorComponent.{c, v, r} J B τ J' uInv uPush adjSet O μ k M N).hom.val.app V
  let b (k : ℕ) := (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients
    O.coefficientTransition k (O.pull.obj M) (O.pull.obj N)).inv.val.app V
  let t (Q : Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition) :=
    ((transition.{c, v, max c v r} J' O.coefficients O.coefficientTransition h).app Q).val.app V
  let T' := ordinaryTensor.{c, v, r} (coefficientSequenceTopology J')
    (systemRing J' O.coefficients O.coefficientTransition) (O.pull.obj M) (O.pull.obj N)
  change d n (t (O.pull.obj T) (s m T z)) = t T' (d m (s m T z))
  calc
    _ = d n (s n T zn) := congrArg (d n) (ht T z)
    _ = b n (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V
        (s n M xn) (s n N yn)) :=
      component_pure.{c, v, r} J B τ J' uInv uPush adjSet O μ hp n M N Z xn yn zn hzn V a
    _ = b n (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V
        (t (O.pull.obj M) (s m M x)) (t (O.pull.obj N) (s m N y))) :=
      congrArg (b n) (congrArg₂
        (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V) (ht M x).symm (ht N y).symm)
    _ = t T' (b m (tensorSection.{c, v, r} J' (O.coefficients m) _ _ V
        (s m M x) (s m N y))) :=
      (tensor_transition_inv_pure.{c, v, r} J' O.coefficients O.coefficientTransition h
        (O.pull.obj M) (O.pull.obj N) V (s m M x) (s m N y)).symm
    _ = _ := congrArg (fun q ↦ t T' q)
      (component_pure.{c, v, r} J B τ J' uInv uPush adjSet O μ hp m M N Z x y z hz V a).symm

end WeilConjectures.SemilinearSections
