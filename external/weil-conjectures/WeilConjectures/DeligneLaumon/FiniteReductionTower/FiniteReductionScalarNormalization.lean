/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import all WeilConjectures.DeligneLaumon.QuotientTensorScalarTowerComparison
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

set_option linter.privateModule false

/-! # Scalar normalization of the strict finite reduction tower

Source: Stacks, Tags 03EK, 06YT and 06YU.
(blueprint: lem-a1-finite-reduction-scalar-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  WeilConjectures.tensorScalarLevelIso
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.unrestrictedIntegralReductionExistence
  WeilConjectures.IntegralOnSlice.reductionWitness
attribute [local implicit_reducible] SheafOfModules.KFlatTotalTensorModel.monoidal
  SheafOfModules.KFlatTotalTensorModel.tensor
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose
  WeilConjectures.IntegralOnSlice.Site WeilConjectures.IntegralOnSlice.siteCategory
  WeilConjectures.IntegralOnSlice.topology
  WeilConjectures.IntegralOnSlice.restrict WeilConjectures.IntegralOnSlice.ring
  WeilConjectures.IntegralOnSlice.finite WeilConjectures.IntegralOnSlice.projection
  WeilConjectures.PrincipalKoszulStrictReplacement.residue
  SheafOfModules.restrictScalars SheafOfModules.unit SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingProjectionUnrestricted
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientCommRingSheaf
attribute [local instance] WeilConjectures.tensorMonoidal WeilConjectures.tensorZero
  WeilConjectures.tensorPreadditive WeilConjectures.tensorObjZero WeilConjectures.tensorHasTotal
attribute [local implicit_reducible] WeilConjectures.tensorMonoidal
  WeilConjectures.PrincipalKoszulStrictReplacement.tensorWith
  WeilConjectures.PrincipalKoszulStrictReplacement.targetTower
  WeilConjectures.PrincipalKoszulStrictReplacement.targetTowerMap
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.ofOpSequence
  CategoryTheory.Functor.ofSequence
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.PrincipalKoszulStrictReplacement
  (sourceTower targetTower sourceTowerMap targetTowerMap comparison residue)
namespace WeilConjectures.FiniteReductionTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : Scheme.{t})

private theorem sliceTransition_eq (n : ℕ) :
    IntegralOnSlice.transition l E Y none n = unrestrictedIntegralTransition l E Y n := by
  apply (unrestrictedIntegralTransition_existsUnique l E Y n).unique
  · exact (IntegralOnSlice.transition_existsUnique l E Y none n).exists.choose_spec
  · exact (unrestrictedIntegralTransition_existsUnique l E Y n).exists.choose_spec

private theorem reduction_step (P : CochainComplex (Modules l E Y) ℤ) (n : ℕ) :
    (((reductionComplex l E Y).obj P).asFunctor).map (homOfLE n.le_succ).op =
      (unrestrictedIntegralTransition l E Y n).app P := by
  apply HomologicalComplex.hom_ext
  intro i
  change (((Functor.ofOpSequence (unrestrictedIntegralTransition l E Y)).map
    (homOfLE n.le_succ).op).app P).f i = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private def scalarTowerIso (P : CochainComplex (Modules l E Y) ℤ) :
    targetTower l E Y P ≅ ((reductionComplex l E Y).obj P).asFunctor := by
  let a : targetTower l E Y P ⟶ ((reductionComplex l E Y).obj P).asFunctor :=
    NatTrans.ofOpSequence (fun n ↦ (tensorScalarLevelIso l E Y n P).hom) (by
      intro n
      rw [reduction_step]
      apply HomologicalComplex.hom_ext
      intro i
      have h := tensorScalarLevelIso_transition l E Y n P
      have ht := congrArg
        (fun τ ↦ (tensorScalarLevelIso l E Y (n + 1) P).hom ≫ τ.app P)
        (sliceTransition_eq l E Y n)
      with_unfolding_all exact congrArg (fun a ↦ a.f i) (h.trans ht))
  exact NatIso.ofComponents (fun n ↦ tensorScalarLevelIso l E Y n.unop P)
    (fun f ↦ a.naturality f)

private theorem scalarTowerIso_hom_app (P : CochainComplex (Modules l E Y) ℤ)
    (n : ℕᵒᵖ) :
    (scalarTowerIso l E Y P).hom.app n = (tensorScalarLevelIso l E Y n.unop P).hom := rfl

attribute [local irreducible] scalarTowerIso

end WeilConjectures.FiniteReductionTower
