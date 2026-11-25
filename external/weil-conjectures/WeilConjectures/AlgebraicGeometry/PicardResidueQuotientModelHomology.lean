/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineResidueCycleHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import WeilConjectures.AlgebraicGeometry.AffineResidueScalarTransport
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
-- The original interface includes E, which is irrelevant to this algebraic comparison.
set_option linter.unusedVariables false in
/-- The explicit residue cycle quotient is additively the degree-one homology
of the scalar extension of sections.  This is the algebraic quotient step of
Tag 010V, independent of the geometric derived comparison.
(blueprint: new-picard-residue-quotient-model-homology) -/
theorem picard_residue_quotient_model_homology
    [∀ Y : Scheme.{v}, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (p : Ideal Γ(W, U)) [p.IsPrime]
    (hp : p = RingHom.ker (W.evaluation U w hwU).hom)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    Nonempty (affineResidueCycleHomology W U p K ≃+ C.homology 1) := by
  classical
  dsimp only
  let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
    SheafOfModules.evaluation _ (.op (Over.mk (𝟙 U)))
  let : F.Additive := inferInstanceAs
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
  let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
  let : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
  let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hp' : p = (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal := by
    rw [hp, hU.isoSpec_hom_apply]
    ext a
    change W.evaluation U w hwU a = 0 ↔
      W.presheaf.germ U w hwU a ∈ IsLocalRing.maximalIdeal _
    exact IsLocalRing.residue_eq_zero_iff _
  clear hp
  subst p
  obtain ⟨δ⟩ := affine_residue_scalar_transport W U hU ⟨w, hwU⟩
  let κ := (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal.ResidueField
  let a : κ ≃ₗ[Γ(W, U)]
      (ModuleCat.restrictScalars (algebraMap Γ(W, U) κ)).obj (ModuleCat.of κ κ) :=
    { AddEquiv.refl κ with
      map_smul' := fun r x ↦ Algebra.smul_def r x }
  let t (j : ℤ) := (TensorProduct.congr a (LinearEquiv.refl Γ(W, U) (F.obj (K.X j))))
  let e (j : ℤ) : affineResidueTerm W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K j ≃+
      C.X j := (t j).toAddEquiv.trans (δ.app (F.obj (K.X j))).toLinearEquiv.toAddEquiv
  have he (i j : ℤ) (x : affineResidueTerm W U
      (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K i) :
      e j (affineResidueDifferential W U _ K i j x) = C.d i j (e i x) := by
    let S := ModuleCat.extendScalars.{v, v, v} (algebraMap Γ(W, U) κ)
    have ht : t j (affineResidueDifferential W U _ K i j x) =
        S.map (F.map (K.d i j)) (t i x) := by
      induction x using TensorProduct.inductionOn with
      | tmul r m => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    change (δ.hom.app (F.obj (K.X j)))
        (t j (affineResidueDifferential W U _ K i j x)) = _
    rw [ht]
    exact ConcreteCategory.congr_hom (δ.hom.naturality (F.map (K.d i j))) (t i x)
  let S := C.sc' 0 1 2
  let ec : affineResidueCycles W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K ≃+
      LinearMap.ker S.g.hom :=
    { toFun := fun x ↦ ⟨e 1 x.val, by
        change C.d 1 2 (e 1 x.val) = 0
        rw [← he, x.property, map_zero]⟩
      invFun := fun x ↦ ⟨(e 1).symm x.val, by
        apply (e 2).injective
        rw [he, (e 1).apply_symm_apply, map_zero]
        exact x.property⟩
      left_inv := fun x ↦ Subtype.ext ((e 1).symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext ((e 1).apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext ((e 1).map_add x.val y.val) }
  have hb : (affineResidueBoundaries W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K).map
      ec.toAddMonoidHom = S.moduleCatToCycles.range.toAddSubgroup := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz⟩ := hy
      refine ⟨e 0 z, ?_⟩
      apply Subtype.ext
      change C.d 0 1 (e 0 z) = e 1 y.val
      rw [← he, hz]
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨ec.symm x, ?_, ec.apply_symm_apply x⟩
      refine ⟨(e 0).symm y, ?_⟩
      change affineResidueDifferential W U _ K 0 1 ((e 0).symm y) = (e 1).symm x.val
      apply (e 1).injective
      rw [he, (e 1).apply_symm_apply, (e 0).apply_symm_apply]
      exact congrArg Subtype.val hy
  let q := QuotientAddGroup.congr
    (affineResidueBoundaries W U (hU.isoSpec.hom ⟨w, hwU⟩).asIdeal K)
    S.moduleCatToCycles.range.toAddSubgroup ec hb
  exact ⟨q.trans ((S.moduleCatHomologyIso.symm ≪≫
    (C.homologyIsoSc' 0 1 2 (by simp) (by simp)).symm).toLinearEquiv.toAddEquiv)⟩
end AlgebraicGeometry.Scheme
