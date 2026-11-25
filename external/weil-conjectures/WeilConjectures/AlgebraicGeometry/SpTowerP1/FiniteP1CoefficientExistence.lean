/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerP1.FiniteP1IntrinsicRootTensor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonPureSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Existence of normalized finite coefficient coordinates

Source: blueprint latest, diagonal-tower trace proof (1), identification of
finite coefficient units and direct images before the Chern-class calculation.
(blueprint: lem-sfb-finite-p1-coefficient-adjunction-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem realizationUnit_naturality (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {M N : FixedSheaves l E n T} (f : M ⟶ N)
    (W : T.ProEtᵒᵖ) (x : M.obj.obj W) :
    ((realization l E n T).map f).val.app W
        (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) M W x) =
      sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) N W (f.hom.app W x) := by
  exact (congrArg (fun k ↦ k.app W x)
    ((PresheafOfModules.sheafificationAdjunction
      (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n))).unit.naturality
        ((finiteCoefficientModulePresheaf T.ProEt (levelRing l E n)).map f.hom))).symm

private def coefficientEvaluationMap (T : Scheme.{u}) (n : ℕ) :
    proEtaleConstantModule T (SpTowerShriek.R l E n) ⟶
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) :=
  SheafOfModules.unitToPushforwardObjUnit
    (eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm)

private theorem coefficientEvaluationMap_isIso (T : Scheme.{u}) (n : ℕ) :
    IsIso (coefficientEvaluationMap l E T n) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [← isIso_iff_of_reflects_iso _ (forget AddCommGrpCat)]
  change IsIso ((forget RingCat).map
    ((eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
        n).symm).hom.app U))
  infer_instance

private theorem coefficientEvaluationMap_sections (T : Scheme.{u}) (n : ℕ)
    (W : T.ProEtᵒᵖ) (a : levelRing l E n) :
    (coefficientEvaluationMap l E T n).val.app W
      ((finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n)).app W a) =
        (toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (levelRing l E n)))).app W a := by
  have h : (eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
        n).symm).hom.app W = 𝟙 _ := by
    change ((sheafToPresheaf (ProEt.topology T) RingCat.{u + 1}).map
      (eqToHom (WeilConjectures.SemilinearSections.evaluation_ring
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
          n).symm)).app W = _
    rw [eqToHom_map, eqToHom_app]
    rfl
  exact congrArg (fun k ↦ k.hom
    ((finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n)).app W a)) h

attribute [local irreducible] coefficientEvaluationMap

/-- The normalized coefficient coordinates at a finite level: the unit coordinate is the
constant-object comparison followed by the realization unit and coefficient evaluation, and
the line coordinate is the root-site comparison followed by the intrinsic root-tensor
comparison.

Source: diagonal-tower trace (1), constant and root sections; Stacks Tags 03CY,
03EK and 0GLZ (blueprint: lem-sfb-finite-p1-coefficient-existence).
Proof: compose the constant-object comparison with the normalized regular-module
realization and coefficient evaluation. Naturality of the realization unit and
the monoidal comparison unit equation give its scalar-section formula. For the
line, compose finiteRootSiteComparison with the intrinsic root-tensor comparison.
Their pure-tensor equations give exactly the required root-section formula. -/
@[no_expose] def finiteP1CoefficientCoordinates (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] (T : Scheme.{u})
    (hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    CoefficientCoordinates l E n T hT := by
  let B := levelRing l E n
  let C := ModuleCat.{u + 1} B
  let F := comparisonUpperStar C T
  let c0 := asIso (Functor.OplaxMonoidal.η F)
  have := coefficientEvaluationMap_isIso l E T n
  let c := (realization l E n T).mapIso c0 ≪≫
    proEtaleConstantModuleUnit T (SpTowerShriek.R l E n) ≪≫
    asIso (coefficientEvaluationMap l E T n)
  let hR := finiteRootSiteComparison B
  let sigma := Classical.choose hR
  have htensor := (Classical.choose_spec (Classical.choose_spec hR)).2.2.1
  let e := Classical.choose (finiteP1_intrinsic_root_tensor l E n T).exists
  have he := Classical.choose_spec (finiteP1_intrinsic_root_tensor l E n T).exists
  refine {
    unit := c
    unit_sections := ?_
    line := (realization l E n T).mapIso
      (sigma _ (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T hT) ≪≫ e
    line_sections := ?_ }
  · intro U W f a
    let x := (((comparisonUpperStar C T).obj
      (Etale.ordinaryFiniteConstant B T)).obj.map f.op
        (((comparisonAdjunction C T).unit.app
          (Etale.ordinaryFiniteConstant B T)).hom.app U
            ((toSheafify T.smallEtaleTopology
              ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of B B))).app U a)))
    have h0 : c0.hom.hom.app W x =
        (toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (ModuleCat.of B B))).app W a :=
      (comparison_pure_sections B T).2 U W f a
    have hn := realizationUnit_naturality l E n T c0.hom W x
    have hr := (proEtaleConstantModuleUnit_existsUnique T
      (SpTowerShriek.R l E n)).exists.choose_spec W a
    exact (congrArg (fun y ↦ (coefficientEvaluationMap l E T n).val.app W
      ((proEtaleConstantModuleUnit T (SpTowerShriek.R l E n)).hom.val.app W y)) hn).trans
      ((congrArg (fun y ↦ (coefficientEvaluationMap l E T n).val.app W
        ((proEtaleConstantModuleUnit T (SpTowerShriek.R l E n)).hom.val.app W
          (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W y))) h0).trans
        ((congrArg (fun y ↦ (coefficientEvaluationMap l E T n).val.app W y) hr).trans
          (coefficientEvaluationMap_sections l E T n W a)))
  · intro U W f a z
    let s := sigma (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (levelAnnihilates l E n) T hT
    let x := (((comparisonUpperStar C T).obj
      (finiteEtaleTateLine T (l ^ (n + 1)) B (levelAnnihilates l E n))).obj.map f.op
        (((comparisonAdjunction C T).unit.app
          (finiteEtaleTateLine T (l ^ (n + 1)) B (levelAnnihilates l E n))).hom.app U
            (finiteEtaleTateOneGenerator B (l ^ (n + 1)) T
              (levelAnnihilates l E n) U a z)))
    have hn := realizationUnit_naturality l E n T s.hom W x
    have hs := htensor (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
      (levelAnnihilates l E n) T hT U W f a z
    exact (congrArg (fun y ↦ e.hom.val.app W y) hn).trans
      ((congrArg (fun y ↦ e.hom.val.app W
        (sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W y)) hs).trans
          (he W a _))

end AlgebraicGeometry.ProEtale.SpTowerP1
