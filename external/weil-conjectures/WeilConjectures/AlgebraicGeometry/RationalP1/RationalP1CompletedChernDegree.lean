/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalCompletedChernLift
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceTwistedSplittingComponents
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleFaithful

/-! # Degree of the whole-system normalized completed Chern adjunct
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1

/-- A whole-system normalized completed Chern adjunct has degree one. -/
theorem completed_chern_degree
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (tq : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤)))
    (c : DiagonalTrace.completedUnit l S ⟶
      tq.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (hc : (diagonalCompletedUnderlying l S).map c ≫
        tq.toPresentation.sourceMap l (ULift.{u} (Padic l)) =
      tq.coefficientsS.unitMap l (ULift.{u} (Padic l)) tq.LS ≫
        tq.LS.R.map (tq.toPresentation.systemChern l)) : c ≫ tq.trace = 𝟙 _ := by
  let E := ULift.{u} (Padic l)
  let p := tq.toPresentation
  let T := p.twistS.T l E ⋙
    shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S)) (2 : ℤ)
  let b := (shiftFunctor (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app
          (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    (shiftFunctorCompIsoId (SpTowerClasses.D S (SpTowerClasses.Arings l E S))
      (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (SpTowerClasses.inverseLine l E p.chernS)) ≪≫
    p.twistS.contract l E
  obtain ⟨_, _, hchern⟩ := DiagonalTrace.diagonalTrace_twistedSplitting_components l p hS
  change p.model.chernAdjoint l E = b.inv ≫ T.map biprod.inr ≫
    T.map (p.model.bq l E) ≫ (p.model.twistedPush l E).hom at hchern
  have ht : p.model.trace l E = (p.model.twistedPush l E).inv ≫
      T.map (inv (p.model.bq l E)) ≫ T.map biprod.snd ≫ b.hom := by rfl
  have hmodel : p.model.chernAdjoint l E ≫ p.model.trace l E = 𝟙 _ := by
    calc
      _ = b.inv ≫ T.map
          (biprod.inr ≫ p.model.bq l E ≫ inv (p.model.bq l E) ≫ biprod.snd) ≫
            b.hom := by
        rw [hchern, ht]
        simp only [Functor.map_comp, Category.assoc,
          (p.model.twistedPush l E).hom_inv_id_assoc]
      _ = 𝟙 _ := by
        simp only [IsIso.hom_inv_id_assoc, biprod.inr_snd, CategoryTheory.Functor.map_id]
        exact (congrArg (b.inv ≫ ·) (Category.id_comp b.hom)).trans b.inv_hom_id
  have hsystem : p.systemChern l ≫ p.systemTrace l E = 𝟙 _ := by
    unfold DiagonalTrace.Presentation.systemChern DiagonalTrace.Presentation.systemTrace
    change (p.restrictionS.F.mapDerivedCategory.map (p.model.chernAdjoint l E) ≫
        p.varying.hom.app ((SpTowerClasses.line l E p.chernX) ⟦(2 : ℤ)⟧)) ≫
      (p.varying.inv.app ((SpTowerClasses.line l E p.chernX) ⟦(2 : ℤ)⟧) ≫
        p.restrictionS.F.mapDerivedCategory.map (p.model.trace l E)) = 𝟙 _
    rw [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
      hmodel, CategoryTheory.Functor.map_id]
  have htrace : (diagonalCompletedUnderlying l S).map tq.trace ≫
      p.coefficientsS.unitMap l E p.LS = p.sourceMap l E ≫
        p.LS.R.map (p.systemTrace l E) := by
    simpa only [DiagonalTrace.Presentation.IsTrace, DiagonalTrace.Presentation.sourceMap,
      Category.assoc] using tq.construction
  have := tq.unit_limit
  apply DiagonalTrace.diagonalTrace_single_map_injective l S
  apply (cancel_mono (p.coefficientsS.unitMap l E p.LS)).mp
  calc
    _ = (diagonalCompletedUnderlying l S).map c ≫
        ((diagonalCompletedUnderlying l S).map tq.trace ≫
          p.coefficientsS.unitMap l E p.LS) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = ((diagonalCompletedUnderlying l S).map c ≫ p.sourceMap l E) ≫
        p.LS.R.map (p.systemTrace l E) := by rw [htrace, Category.assoc]
    _ = (p.coefficientsS.unitMap l E p.LS ≫ p.LS.R.map (p.systemChern l)) ≫
        p.LS.R.map (p.systemTrace l E) := by rw [hc]
    _ = p.coefficientsS.unitMap l E p.LS := by
      rw [Category.assoc, ← Functor.map_comp, hsystem,
        CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by rw [CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.RationalP1
