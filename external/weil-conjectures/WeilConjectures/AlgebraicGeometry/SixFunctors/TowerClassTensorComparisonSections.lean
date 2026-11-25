/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorComparison
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorComponentHorizontal
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryTensor
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorComponentHorizontal
import all WeilConjectures.AlgebraicGeometry.System.SystemOrdinaryTensorReduction
import all WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorEvaluation

/-! # Generalized unit sections of the ordinary tensor comparison

## References

* Stacks 03EL
* Zheng Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.SemilinearSections
section
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (L : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (P : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r))) (a : L ⊣ P)
    (O : GeometryOrdinary.{c, v, r} J B τ J' L P a)
    (T : GeometryOrdinaryTensor.{c, v, r} J B τ J' L P a O)

/-- Evaluation of a system tensor comparison is its specified geometric component. -/
theorem tensorComparison_evaluation (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ) :
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
        (T.system M N).hom =
      (geometricTensorComponent.{c, v, r} J B τ J' L P a O T.level n M N).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O.coefficients n)
  let := SheafOfModules.monoidalCategory (O.coefficients n)
  let : IsIso (ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
      ((O.ordinaryPullEvaluation n).hom.app M)
      ((O.ordinaryPullEvaluation n).hom.app N)) := by
    change IsIso (_ ⊗ₘ _)
    infer_instance
  apply (cancel_mono ((ordinaryEvaluationTensor.{c, v, r} J'
    O.coefficients O.coefficientTransition n (O.pull.obj M) (O.pull.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J' (O.coefficients n)
        ((O.ordinaryPullEvaluation n).hom.app M)
        ((O.ordinaryPullEvaluation n).hom.app N))).mp
  simpa only [Category.assoc] using
    (T.evaluation n M N).trans
      (component_square.{c, v, r} J B τ J' L P a O T.level n M N).symm

attribute [local irreducible] evaluation tensorSection ordinaryEvaluationTensor
attribute [local irreducible] systemRing rings ringPresheaf coefficientMap
variable (U : Cᵒᵖ) (V : C'ᵒᵖ)
    (s : ∀ Z : Sheaf J (Type (max c v r)), Z.obj.obj U → (L.obj Z).obj.obj V)
    (hs : ∀ {Z W : Sheaf J (Type (max c v r))} (f : Z ⟶ W) (b : Z.obj.obj U),
      (L.map f).hom.app V (s Z b) = s W (f.hom.app U b))

private def unitImage (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).obj
      (O.pull.obj M)).val.obj V :=
  (imageIdentification.{c, v, r} J B τ J' L P a O n M).inv.hom.app V
    (s _ x)

include hs in
private theorem unitImage_map (n : ℕ) {M N : Systems.{c, v, max c v r} J B τ}
    (f : M ⟶ N)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (O.pull.map f)).val.app V (unitImage.{c, v, r} J B τ J' L P a O U V s n M x) =
    unitImage.{c, v, r} J B τ J' L P a O U V s n N
      (((evaluation.{c, v, max c v r} J B τ n).map f).val.app U x) := by
  dsimp only [unitImage, imageIdentification, Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv]
  have h₁ := congrArg (fun k ↦ k.val.app V
    (((O.inverseImage n).moduleUnderlying.inv.app _).hom.app V (s _ x)))
    ((O.ordinaryPullEvaluation n).inv.naturality f)
  have h₂ := congrArg (fun k ↦ k.hom.app V (s _ x))
    ((O.inverseImage n).moduleUnderlying.inv.naturality
      ((evaluation.{c, v, max c v r} J B τ n).map f))
  change _ = ((O.ordinaryPullEvaluation n).inv.app N).val.app V
    (((O.inverseImage n).moduleUnderlying.inv.app _).hom.app V (s _ _))
  have h₃ := hs ((underlying.{c, v, r} J (B n)).map
    ((evaluation.{c, v, max c v r} J B τ n).map f)) x
  change (L.map ((underlying.{c, v, r} J (B n)).map
    ((evaluation.{c, v, max c v r} J B τ n).map f))).hom.app V (s _ x) =
      s _ (((evaluation.{c, v, max c v r} J B τ n).map f).val.app U x) at h₃
  exact h₁.symm.trans
    (congrArg (((O.ordinaryPullEvaluation n).inv.app N).val.app V)
      (h₂.symm.trans
        (congrArg (((O.inverseImage n).moduleUnderlying.inv.app _).hom.app V) h₃)))

include hs in
private theorem system_unit_pure
    (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U)
    (y : ((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U) :
    ((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (T.system M N).hom).val.app V
      (unitImage.{c, v, r} J B τ J' L P a O U V s n _
        ((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U
          (tensorSection.{c, v, r} J (B n) _ _ U x y))) =
    (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients O.coefficientTransition n
      (O.pull.obj M) (O.pull.obj N)).inv.val.app V
      (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V
        (unitImage.{c, v, r} J B τ J' L P a O U V s n M x)
        (unitImage.{c, v, r} J B τ J' L P a O U V s n N y)) := by
  let Mₙ := (evaluation.{c, v, max c v r} J B τ n).obj M
  let Nₙ := (evaluation.{c, v, max c v r} J B τ n).obj N
  let Z := (underlying.{c, v, r} J (B n)).obj Mₙ ⊗
    (underlying.{c, v, r} J (B n)).obj Nₙ
  let p : Z ⟶ (underlying.{c, v, r} J (B n)).obj Mₙ :=
    CartesianMonoidalCategory.fst _ _
  let q : Z ⟶ (underlying.{c, v, r} J (B n)).obj Nₙ :=
    CartesianMonoidalCategory.snd _ _
  let z := purePair.{c, v, r} J (B n) Mₙ Nₙ ≫
    (underlying.{c, v, r} J (B n)).map
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv
  have hz (W : Cᵒᵖ) (b : Z.obj.obj W) :
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app W
        (z.hom.app W b) =
      tensorSection.{c, v, r} J (B n) Mₙ Nₙ W (p.hom.app W b) (q.hom.app W b) := by
    exact congrArg (fun k ↦ k.val.app W
      (tensorSection.{c, v, r} J (B n) Mₙ Nₙ W b.1 b.2))
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv_hom_id
  have hpure := component_pure.{c, v, r} J B τ J' L P a O T.level T.level_pure
    n M N Z p q z hz V (s Z (x, y))
  have he := congrArg (fun k ↦ k.val.app V
    ((imageMap.{c, v, r} J B τ J' L P a O n _ z).hom.app V (s Z (x, y))))
    (tensorComparison_evaluation.{c, v, r} J B τ J' L P a O T n M N)
  have h := he.trans hpure
  have him (K : Systems.{c, v, max c v r} J B τ)
      (f : Z ⟶ (underlying.{c, v, r} J (B n)).obj
        ((evaluation.{c, v, max c v r} J B τ n).obj K)) :
      (imageMap.{c, v, r} J B τ J' L P a O n K f).hom.app V (s Z (x, y)) =
        unitImage.{c, v, r} J B τ J' L P a O U V s n K (f.hom.app U (x, y)) := by
    change (imageIdentification.{c, v, r} J B τ J' L P a O n K).inv.hom.app V
      ((L.map f).hom.app V (s Z (x, y))) = _
    exact congrArg
      ((imageIdentification.{c, v, r} J B τ J' L P a O n K).inv.hom.app V)
      (hs f (x, y))
  have hleft := congrArg
    (((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (T.system M N).hom).val.app V) (him _ z)
  have hright := congrArg₂
    (fun a b ↦ (ordinaryEvaluationTensor.{c, v, r} J' O.coefficients
      O.coefficientTransition n (O.pull.obj M) (O.pull.obj N)).inv.val.app V
        (tensorSection.{c, v, r} J' (O.coefficients n) _ _ V a b))
    (him _ p) (him _ q)
  exact hleft.symm.trans (h.trans hright)

private def sectionImage (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (x : M.val.obj (op (n, U.unop))) : (O.pull.obj M).val.obj (op (n, V.unop)) :=
  cast (evaluation_carrier.{c, v, r} J' O.coefficients O.coefficientTransition n
    (O.pull.obj M) V)
    (unitImage.{c, v, r} J B τ J' L P a O U V s n M (evalSection.{c, v, r} J B τ n M U x))

private theorem sectionImage_eval (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (x : M.val.obj (op (n, U.unop))) :
    evalSection.{c, v, r} J' O.coefficients O.coefficientTransition n (O.pull.obj M) V
      (sectionImage.{c, v, r} J B τ J' L P a O U V s n M x) =
      unitImage.{c, v, r} J B τ J' L P a O U V s n M
        (evalSection.{c, v, r} J B τ n M U x) := by
  dsimp only [sectionImage, evalSection]
  simp only [cast_cast, cast_eq]

private theorem bridge_evaluation_pure (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    ((evaluation.{c, v, max c v r} J B τ n).map
      ((AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso.{c, v, r}
        (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) N).hom.app M)).val.app U
      (evalSection.{c, v, r} J B τ n _ U (SheafOfModules.siteSheafTensorTmul M N
        (op (n, U.unop)) x y)) =
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U
        (tensorSection.{c, v, r} J (B n) _ _ U
          (evalSection.{c, v, r} J B τ n M U x) (evalSection.{c, v, r} J B τ n N U y)) := by
  rw [evaluation_map_section.{c, v, r} J B τ n,
    AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso_pure.{c, v, r}]
  exact (evaluation_inv_pure_cast.{c, v, r} J B τ n M N U x y).symm

include hs in
private theorem site_unit_pure (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    let e := AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso.{c, v, r}
      (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) N
    let e' :=
      AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso.{c, v, r}
        (coefficientSequenceTopology J')
        (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition) (O.pull.obj N)
    (O.pull.map (e.hom.app M) ≫ (T.system M N).hom ≫ e'.inv.app (O.pull.obj M)).val.app
        (op (n, V.unop))
      (sectionImage.{c, v, r} J B τ J' L P a O U V s n _
        (SheafOfModules.siteSheafTensorTmul M N (op (n, U.unop)) x y)) =
      SheafOfModules.siteSheafTensorTmul (O.pull.obj M) (O.pull.obj N)
        (op (n, V.unop))
        (sectionImage.{c, v, r} J B τ J' L P a O U V s n M x)
        (sectionImage.{c, v, r} J B τ J' L P a O U V s n N y) := by
  let e := AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso.{c, v, r}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) N
  let e' := AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates.siteTensorIso.{c, v, r}
    (coefficientSequenceTopology J')
    (systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition) (O.pull.obj N)
  have h := system_unit_pure.{c, v, r} J B τ J' L P a O T U V s hs n M N
    (evalSection.{c, v, r} J B τ n M U x) (evalSection.{c, v, r} J B τ n N U y)
  rw [← bridge_evaluation_pure.{c, v, r} J B τ U n M N x y] at h
  have hm := unitImage_map.{c, v, r} J B τ J' L P a O U V s hs n (e.hom.app M)
    (evalSection.{c, v, r} J B τ n _ U
      (SheafOfModules.siteSheafTensorTmul M N (op (n, U.unop)) x y))
  change _ = unitImage.{c, v, r} J B τ J' L P a O U V s n
    (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) M N)
    (((evaluation.{c, v, max c v r} J B τ n).map (e.hom.app M)).val.app U
      (evalSection.{c, v, r} J B τ n _ U
        (SheafOfModules.siteSheafTensorTmul M N (op (n, U.unop)) x y))) at hm
  rw [← hm] at h
  have ht := bridge_evaluation_pure.{c, v, r} J' O.coefficients O.coefficientTransition V n
    (O.pull.obj M) (O.pull.obj N)
    (sectionImage.{c, v, r} J B τ J' L P a O U V s n M x)
    (sectionImage.{c, v, r} J B τ J' L P a O U V s n N y)
  rw [sectionImage_eval.{c, v, r}, sectionImage_eval.{c, v, r}] at ht
  have h' := h.trans ht.symm
  have hh := congrArg
    (((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (e'.inv.app (O.pull.obj M))).val.app V) h'
  change (((evaluation.{c, v, max c v r} J' O.coefficients
      O.coefficientTransition n).map (O.pull.map (e.hom.app M)) ≫
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (T.system M N).hom ≫
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (e'.inv.app (O.pull.obj M))).val.app V)
    (unitImage.{c, v, r} J B τ J' L P a O U V s n _
      (evalSection.{c, v, r} J B τ n _ U
        (SheafOfModules.siteSheafTensorTmul M N (op (n, U.unop)) x y))) =
    (((evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (e'.hom.app (O.pull.obj M)) ≫
    (evaluation.{c, v, max c v r} J' O.coefficients O.coefficientTransition n).map
      (e'.inv.app (O.pull.obj M))).val.app V)
    (evalSection.{c, v, r} J' O.coefficients O.coefficientTransition n _ V
      (SheafOfModules.siteSheafTensorTmul (O.pull.obj M) (O.pull.obj N)
        (op (n, V.unop))
        (sectionImage.{c, v, r} J B τ J' L P a O U V s n M x)
        (sectionImage.{c, v, r} J B τ J' L P a O U V s n N y))) at hh
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    e'.hom_inv_id_app, CategoryTheory.Functor.map_id] at hh
  rw [← sectionImage_eval.{c, v, r} J B τ J' L P a O U V s n _
    (SheafOfModules.siteSheafTensorTmul M N (op (n, U.unop)) x y)] at hh
  rw [evaluation_map_section.{c, v, r}] at hh
  have hh' := congrArg
    (cast (evaluation_carrier.{c, v, r} J' O.coefficients O.coefficientTransition n
      ((SheafOfModules.siteSheafTensorRight
        (A := systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        (O.pull.obj N)).obj (O.pull.obj M)) V)) hh
  simpa only [evalSection, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply, cast_cast, cast_eq] using hh'

end
end WeilConjectures.SemilinearSections
