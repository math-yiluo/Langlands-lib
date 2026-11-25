/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback

import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralCoefficientPullbackExistence
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerRestrictedScalarAdjunction
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineTransitionTensor
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLinePullbackLowerTensor
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionSectionNaturality

/-! # Core finite-level root normalization comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  SemilinearSections.transition SemilinearSections.coefficientMap
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
  PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
  Scheme.ProEt spCoefficientCommRings SpTowerShriek.tau SemilinearSections.evaluation
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage

private theorem rootTranspose
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (n : ℕ) :
    (((abAdjunction f).homEquiv _ _) d.kummer.τ₁).app (op n) =
      Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)) := by
  have : Mono (Scheme.proEtaleRootsOfUnityInclusion X (l ^ (n + 1))) := by
    dsimp only [Scheme.proEtaleRootsOfUnityInclusion]
    infer_instance
  have hd : d.kummer.τ₁.app (op n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)) := by
    apply (cancel_mono (Scheme.proEtaleRootsOfUnityInclusion X (l ^ (n + 1)))).1
    have h := NatTrans.congr_app d.kummer.comm₁₂ (op n)
    change d.kummer.τ₁.app (op n) ≫ cX.kummer.inclusion.app (op n) =
      (upperStar AddCommGrpCat.{u + 1} f).map (cY.kummer.inclusion.app (op n)) ≫
        d.kummer.τ₂.app (op n) at h
    rw [cY.kummer.inclusion_eq n, cX.kummer.inclusion_eq n, hk n] at h
    exact h.trans (roots_units_square f (l ^ (n + 1)))
  change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _)
    (d.kummer.τ₁.app (op n)) = _
  rw [hd]
  exact Equiv.apply_symm_apply _ _

private theorem scalarUnitSection
    {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U) :
    HEq ((((c.reduction.forget.F.map
      (c.scalar.ordinaryAdjunction.unit.app c.rootModule)).app (op n)).hom.app U) x)
      ((lineEvaluation l E c n).inv.val.app U
        (Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
          U.unop 1 ((c.rootForget.hom.app (op n)).hom.app U x))) := by
  let y := (eqToHom (c.reduction.forget.sections c.rootModule n U)) x
  have hy : HEq y x := transportAddSection _ x
  have hm := heq_app (c.reduction.forget.sections c.rootModule n U)
    (c.reduction.forget.sections _ n U)
    (c.reduction.forget.morphisms (c.scalar.ordinaryAdjunction.unit.app c.rootModule) n U)
    hy.symm
  have hn := lineScalarSection_normalization l E c n U y x hy
  have hu : lineScalarSection l E c n U y =
      (c.scalar.ordinaryAdjunction.unit.app c.rootModule).val.app (op (n, U.unop)) y := by
    unfold lineScalarSection
    exact SemilinearSections.section_unit.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) y
  rw [hu] at hn
  have hi := congrArg (fun a ↦ a.val.app U
    ((c.scalar.ordinaryAdjunction.unit.app c.rootModule).val.app (op (n, U.unop)) y))
    (lineEvaluation l E c n).hom_inv_id
  have ht := congrArg (fun w ↦ (lineEvaluation l E c n).inv.val.app U w) hn
  exact hm.trans (heq_of_eq (hi.symm.trans ht))

/-- The scalar-unit/geometric-transpose value at one finite level and chart. -/
def scalarRootCoreSource
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (θ₁ : LinePullback l E f g cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :=
  (((cY.reduction.forget.F.map
    ((cY.scalar.ordinaryAdjunction.unit.app cY.rootModule) ≫
      (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l E Y)).map
        (g.ordinaryAdjunction.homEquiv _ _ θ₁.iso.hom))).app n).hom.app U) x

/-- The abelian-transpose value at one finite level and chart. -/
def scalarRootCoreRight
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :=
  (((((abAdjunction f).homEquiv _ _)
    (d.forgetIso.hom.app cY.rootModule ≫
      cX.reduction.forget.F.map
        ((cX.scalar.ordinaryAdjunction.homEquiv _ _)
          (cX.scalar.model.E.map d.rootIso.hom)))).app n).hom.app U) x

private theorem sourceSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (θ : LinePullback l E f g cY cX) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((cY.reduction.forget.F.obj cY.rootModule).obj (op n)).obj.obj U) :
    HEq (scalarRootCoreSource l E f b g cY cX θ (op n) U x)
      ((lineEvaluation l E cX n).inv.val.app (chart f U)
        (Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop 1
          (restrictRoot l f n U ((cY.rootForget.hom.app (op n)).hom.app U x)))) := by
  let t := (g.ordinaryAdjunction.homEquiv _ _) θ.iso.hom
  let R := SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E Y)
  let y := (lineEvaluation l E cY n).inv.val.app U
    (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
      U.unop 1 ((cY.rootForget.hom.app (op n)).hom.app U x))
  have hu := scalarUnitSection l E cY n U x
  have hm := heq_app (cY.reduction.forget.sections (R.obj (lineModule l E cY)) n U)
    (cY.reduction.forget.sections (R.obj (g.push.obj (lineModule l E cX))) n U)
    (cY.reduction.forget.morphisms (R.map t) n U) hu
  have hp := pushEvaluationSections l E g n (lineModule l E cX) U
    (t.val.app (op (n, U.unop)) y)
  have hn := θ.normalization n U 1 ((cY.rootForget.hom.app (op n)).hom.app U x)
  have hi := congrArg (fun a ↦ a.val.app (chart f U)
    (adjointSection l E g θ.iso.hom n U y)) (lineEvaluation l E cX n).hom_inv_id
  change (lineEvaluation l E cX n).hom.val.app (chart f U)
    (adjointSection l E g θ.iso.hom n U y) = _ at hn
  rw [map_one] at hn
  have ht := congrArg (fun w ↦ (lineEvaluation l E cX n).inv.val.app (chart f U) w) hn
  have he : HEq (t.val.app (op (n, U.unop)) y)
      (adjointSection l E g θ.iso.hom n U y) := hp.symm
  unfold scalarRootCoreSource
  rw [Functor.map_comp]
  exact hm.trans (he.trans (heq_of_eq (hi.symm.trans ht)))

private theorem rightSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : ((cY.reduction.forget.F.obj cY.rootModule).obj (op n)).obj.obj U) :
    HEq (scalarRootCoreRight l E f cY cX d (op n) U x)
      ((lineEvaluation l E cX n).inv.val.app (chart f U)
        (Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop 1
          (restrictRoot l f n U ((cY.rootForget.hom.app (op n)).hom.app U x)))) := by
  let δ := d.forgetIso.hom.app cY.rootModule ≫ cX.reduction.forget.F.map d.rootIso.hom
  let r := (abAdjunction f).homEquiv _ _ δ
  have hr : cY.rootForget.inv ≫ r ≫ (abPush f).map cX.rootForget.hom =
      (abAdjunction f).homEquiv _ _ d.kummer.τ₁ := by
    rw [d.kummer_roots, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
    rfl
  have hr' := congrArg (fun k ↦ cY.rootForget.hom ≫ k) hr
  simp only [← Category.assoc, cY.rootForget.hom_inv_id, Category.id_comp] at hr'
  have hz := congrArg (fun k ↦ (k.app (op n)).hom.app U x) hr'
  change (cX.rootForget.hom.app (op n)).hom.app (chart f U)
      ((r.app (op n)).hom.app U x) =
    ((((abAdjunction f).homEquiv _ _) d.kummer.τ₁).app (op n)).hom.app U
      ((cY.rootForget.hom.app (op n)).hom.app U x) at hz
  rw [rootTranspose l E f cY cX d hk n] at hz
  have hroot := root_direct_eq l f n U
    ((cY.rootForget.hom.app (op n)).hom.app U x)
  have hz' := hz.trans hroot
  have hs : (cX.scalar.ordinaryAdjunction.homEquiv _ _)
      (cX.scalar.model.E.map d.rootIso.hom) =
      d.rootIso.hom ≫ cX.scalar.ordinaryAdjunction.unit.app cX.rootModule := by
    rw [Adjunction.homEquiv_unit]
    exact (cX.scalar.ordinaryAdjunction.unit.naturality d.rootIso.hom).symm
  have hu := scalarUnitSection l E cX n (chart f U) ((r.app (op n)).hom.app U x)
  rw [hz'] at hu
  unfold scalarRootCoreRight
  rw [hs, Functor.map_comp, ← Category.assoc, Adjunction.homEquiv_naturality_right]
  exact hu

/--
The finite root normalization comparison after expanding both scalar adjunction
transposes to their units.  This is the χ-free core of the component calculation.

Source: blueprint latest, classes proof (2), finite-level evaluation of the
abelian transpose before assembling the tower map; Stacks 03EL.
(blueprint: lem-sp-tower-scalar-root-abelian-transpose-component-core)

Proof: evaluate the scalar unit as the sheafified pure tensor, evaluate the
ordinary geometric transpose on that tensor, and use the normalized line
comparison.  The Kummer boundary square, `hk`, and `d.kummer_roots` identify
its root with `restrictRoot`; `LinePullback.normalization` then gives the
same finite Tate tensor as the abelian transpose after `d.rootIso`.
-/
theorem scalarRoot_abelianTranspose_core
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (cY : Chern l E Y) (cX : Chern l E X)
    (d : IntegralCoefficientPullback l E f cY cX)
    (hk : ∀ n : ℕ, d.kummer.τ₂.app (op n) = (unitsPull f).app (op n))
    (θ₁ : LinePullback l E f g cY cX)
    (n : ℕᵒᵖ) (U : Y.ProEtᵒᵖ)
    (x : (((cY.reduction.forget.F.obj cY.rootModule).obj n).obj.obj U)) :
    HEq (scalarRootCoreSource l E f b g cY cX θ₁ n U x)
      (scalarRootCoreRight l E f cY cX d n U x) := by
  exact (sourceSection l E f b g cY cX θ₁ n.unop U x).trans
    (rightSection l E f cY cX d hk n.unop U x).symm

end AlgebraicGeometry.ProEtale.SpTowerClasses
