/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeStrictCoefficientEquations
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeLambdaDirectImage

/-! # reconstructionCoefficientEquations

## References

* Stacks Tags 099M, 099N, 0A07 and 0E48
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

section Helpers

variable {U V : Scheme.{t}} (u : U ⟶ V)

/-- The ordinary-to-completed comparison followed by the reduction/pullback reconstruction
is the completion unit of the ordinary pullback. -/
theorem ordinaryToCompleted_reconstruction (M : d.derived V) :
    d.ordinaryToCompleted u M ≫
        (completedRlim U (d.completedRing U)).map ((d.reductionTowerPullbackIso u).hom.app M) =
      d.completionUnit U ((d.pull u).obj M) := by
  have he : d.reductionTowerPullbackIso u = stratumReductionIso d u :=
    (completedReductionPullbackIso_existsUnique d u).unique
      (completedReductionPullbackIso_existsUnique d u).choose_spec.1
      (stratumReductionIso_exists d u).exists.choose_spec
  have ha := stratumReduction_augmentation d u M
  rw [← he] at ha
  unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
  rw [Category.assoc, ← Functor.map_comp, Category.assoc, ha, Iso.inv_hom_id_app_assoc]

/-- The explicit completed pullback/scalar comparison, built from the reconstruction of
completed pullback, `lambda`, `rho` and `alpha`. -/
def completedPullResIso :
    inclusion d V ⋙ d.completedPull u ⋙ res d U ≅
      inclusion d V ⋙ res d V ⋙ completePull d u :=
  NatIso.ofComponents
    (fun M ↦ (res d U).mapIso ((completedRlim U (d.completedRing U)).mapIso
        ((d.reductionTowerPullbackIso u).app M.obj)) ≪≫
      (lambda d U).app ((completedReductionTower U d).obj ((d.pull u).obj M.obj)) ≪≫
      (rlim (A := A) U).mapIso ((rho d U).app ((d.pull u).obj M.obj) ≪≫
        (reduction d U).mapIso ((alpha d u).app M.obj)))
    (by
      intro M N a
      have h1 := (d.reductionTowerPullbackIso u).hom.naturality a.hom
      have h2 := (lambda d U).hom.naturality
        ((completedReductionTower U d).map ((d.pull u).map a.hom))
      have h3 := (rho d U).hom.naturality ((d.pull u).map a.hom)
      have h4 := (alpha d u).hom.naturality a.hom
      dsimp only [Functor.comp_map, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom,
        Iso.app_hom, ObjectProperty.ι_map, AdicCoefficientDatum.completedPull] at h1 h2 h3 h4 ⊢
      rw [← Functor.map_comp_assoc, ← Functor.map_comp, h1, Functor.map_comp, Functor.map_comp,
        Category.assoc, reassoc_of% h2, ← Functor.map_comp, reassoc_of% h3,
        ← Functor.map_comp, h4, Functor.map_comp]
      simp only [Functor.map_comp, Category.assoc]
      rfl)

/-- The explicit comparison satisfies the completion-unit equation characterizing `phi`. -/
theorem completedPullResIso_unit (M : AComplete d V) :
    (res d U).map (d.ordinaryToCompleted u M.obj) ≫ (completedPullResIso d u).hom.app M =
      (alpha d u).hom.app M.obj ≫
        (unit d U).app ((pull (A := A) u).obj ((res d V).obj M.obj)) := by
  simp only [completedPullResIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp_assoc, ordinaryToCompleted_reconstruction, Functor.map_comp (rlim U),
    reassoc_of% (rho_unit_second d U ((d.pull u).obj M.obj))]
  exact ((unit d U).naturality ((alpha d u).hom.app M.obj)).symm

/-- `phi` is the explicit comparison `completedPullResIso`. -/
theorem phi_eq_completedPullResIso : phi d u = completedPullResIso d u :=
  (phi_existsUnique d u).unique (phi_existsUnique d u).exists.choose_spec
    (completedPullResIso_unit d u)

end Helpers

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The source reconstruction equation. -/
theorem sourceReconstruction_iotaS (K : d.derived X) (hK : d.TowerComplete X K) :
    (res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
        (lambda d Y').hom.app
          ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
        (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
      (iotaS (f := f) (g := g) d K hK).hom := by
  simp only [iotaS, sourceReconstruction, rhoM, phi_eq_completedPullResIso, completedPullResIso,
    Iso.trans_hom, Iso.app_hom, NatIso.ofComponents_hom_app, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

/-- The target reconstruction equation. -/
theorem lambda_rhoPull (K : d.derived X) (hK : d.TowerComplete X K) :
    (lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
        (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
      (phi d g').hom.app ⟨K, hK⟩ ≫ (reconstruction d g' ((res d X).obj K)).hom := by
  have hP := rho_reductionTowerPullbackIso d g' K
  have hL := (lambda d X').hom.naturality ((d.reductionTowerPullbackIso g').hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hL
  simp only [phi_eq_completedPullResIso, completedPullResIso, reconstruction, rhoPull,
    Iso.trans_hom, Iso.app_hom, NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  have hP' : (exchangeResPull d g').hom.app ((completedReductionTower X d).obj K) ≫
      (exchangeConstantPull (A := A) g').map ((rho d X).hom.app K) =
    (exchangeTowerRes d X').map ((d.reductionTowerPullbackIso g').hom.app K) ≫
      (rho d X').hom.app ((d.pull g').obj K) ≫
      (reduction d X').map ((alpha d g').hom.app K) ≫
      (reductionPullIso d g').inv.app ((res d X).obj K) := by
    rw [reassoc_of% hP, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  rw [reassoc_of% hL]
  refine congrArg ((lambda d X').hom.app _ ≫ ·) ?_
  rw [← Functor.map_comp, hP']
  simp only [Functor.map_comp]

/-- The source equation for `sourceA`. -/
theorem sourceA_beta (K : d.derived X) (hK : d.TowerComplete X K) :
    (res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
        (lambda d Y').hom.app
          ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
        (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
      (iotaS (f := f) (g := g) d K hK).hom ≫ (S (f := f) (g := g) d ((res d X).obj K)).hom := by
  have h1 := sourceReconstruction_iotaS (f := f) (g := g) d K hK
  have h2 := exchangeRealizationH_beta (f := f) (g := g) d K
  have hL := (lambda d Y').hom.naturality
    ((d.reductionTowerPullbackIso g).hom.app ((d.push f).obj K))
  have hL' := (lambda d Y').hom.naturality
    ((d.towerPull g).map (d.towerProjection f K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hL hL'
  rw [← h1]
  simp only [S, sourceA, sourceReconstruction, AdicCoefficientDatum.towerH,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom, Category.assoc]
  rw [reassoc_of% hL', reassoc_of% hL]
  refine congrArg ((lambda d Y').hom.app _ ≫ ·) ?_
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  refine congrArg (rlim (A := A) Y').map ?_
  rw [← h2]
  simp only [exchangeRealizationH, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, asIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (exchangeTowerRes d Y'), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The target equation for `targetA`. -/
theorem targetA_delta (K : d.derived X) (hK : d.TowerComplete X K) :
    (res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
        (lambda d Y').hom.app
          ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
        (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
      (iotaT (f' := f') (g' := g') d K hK).hom ≫
        (T (f' := f') (g' := g') d ((res d X).obj K)).hom := by
  have h2 := lambda_rhoPull (g' := g') d K hK
  have hR := lambda_directImageRlimIso_aux d f'
    ((d.towerPull g').obj ((completedReductionTower X d).obj K))
  simp only [targetA, delta, iotaT, T, exchangeCornerD, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  have h2' : (push (A := A) f').map ((phi d g').hom.app ⟨K, hK⟩) ≫
      (push (A := A) f').map (reconstruction d g' ((res d X).obj K)).hom =
    (push (A := A) f').map
        ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
      (push (A := A) f').map ((rlim (A := A) X').map (rhoPull (g' := g') d K).hom) := by
    rw [← Functor.map_comp, ← Functor.map_comp, h2]
  have hD := (directLimitIso (A := A) f').hom.naturality (rhoPull (g' := g') d K).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hD
  rw [reassoc_of% hR, reassoc_of% h2']
  refine congrArg ((chi d f').hom.app _ ≫ ·) ?_
  refine congrArg (_ ≫ ·) ?_
  rw [hD]
  refine congrArg (_ ≫ ·) ?_
  simp only [rhoPull, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp]
  simp only [Iso.symm_hom, Functor.associator_inv_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option linter.unusedVariables false in
/-- For tower-complete `K`, the reconstruction isomorphisms `iotaS`, `iotaT` and `phi` are
compatible with `rhoM`, `rhoPull`, `beta` and `delta` after applying `lambda` and `rlim`. -/
theorem reconstructionCoefficientEquations (sq : ChosenCartesianSquare g' f' f g) :
    ∀ (K : d.derived X) (hK : d.TowerComplete X K),
      ((res d Y').map (sourceReconstruction (f := f) (g := g) d K).hom ≫
          (lambda d Y').hom.app
            ((completedReductionTower Y' d).obj ((d.pull g).obj ((d.push f).obj K))) ≫
          (rlim (A := A) Y').map (rhoM (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom) ∧
      ((lambda d X').hom.app ((d.towerPull g').obj ((completedReductionTower X d).obj K)) ≫
          (rlim (A := A) X').map (rhoPull (g' := g') d K).hom =
        (phi d g').hom.app ⟨K, hK⟩ ≫
          (reconstruction d g' ((res d X).obj K)).hom) ∧
      ((res d Y').map (sourceA (f := f) (f' := f') (g := g) (g' := g') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPull g).obj ((d.towerPush f).obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (beta (f := f) (g := g) d K).hom =
        (iotaS (f := f) (g := g) d K hK).hom ≫
          (S (f := f) (g := g) d ((res d X).obj K)).hom) ∧
      ((res d Y').map (targetA (g' := g') (f' := f') d K).hom ≫
          (lambda d Y').hom.app
            ((d.towerPush f').obj ((d.towerPull g').obj ((completedReductionTower X d).obj K))) ≫
          (rlim (A := A) Y').map (delta (f' := f') (g' := g') d K).hom =
        (iotaT (f' := f') (g' := g') d K hK).hom ≫
          (T (f' := f') (g' := g') d ((res d X).obj K)).hom) := by
  intro K hK
  exact ⟨sourceReconstruction_iotaS d K hK, lambda_rhoPull d K hK, sourceA_beta d K hK,
    targetA_delta d K hK⟩

end AlgebraicGeometry.Scheme.OrderedExchange
