/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernBaseChangeChernSome
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1ClosureExchangeNaturality

/-! The closure-coefficient Chern exchange for canonical normalized lifts. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedScalars

private theorem remove_endpoint_isos
    {C : Type*} [Category C] {A B D E T : C}
    (u : A ≅ B) (j : D ≅ E) (f : A ⟶ T) (g : T ⟶ E) (y : B ⟶ D)
    (h : f ≫ g = u.hom ≫ y ≫ j.hom) : u.inv ≫ f ≫ g ≫ j.inv = y := by
  have he := congrArg (fun v ↦ u.inv ≫ v ≫ j.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using he

-- Elaborating the finite and closure derived endpoint comparisons needs this budget.
/-- The geometric closure-coefficient exchange produces a normalized pair of
completed Chern lifts.  The lifts are existential here; their uniqueness is a
separate statement, so this is the concrete geometric exchange obligation
below the arbitrary-input theorem. -/
theorem scalar_chern_base_change_chern_none_canonical
    (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤))) :
    ∃ a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧),
      CompletedChernNormalized l r.tq.toPresentation a ∧
    ∃ b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧),
      CompletedChernNormalized l r.t₂.toPresentation b ∧
      (let Λ := (coefficient l none).X
       let cq := scalarQChern l none Y r a
       let c₂ := scalarP2Chern l none Y r b
       let F := moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)
       F.map cq ≫ secondTraceExchange l none k p hpl Y =
           (scalarUnitPullIso Λ Y).hom ≫ c₂) := by
  obtain ⟨a, ha⟩ :=
    DiagonalTrace.diagonalTrace_completedChern_lift l r.tq.toPresentation hY
  obtain ⟨b, hb⟩ :=
    DiagonalTrace.diagonalTrace_completedChern_lift l r.t₂.toPresentation hP
  refine ⟨a, ha, b, hb, ?_⟩
  let E := bottomField l
  let x := extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E)
    (ProjectiveLine Y ↘ Y) ((family.toRational E).units Y) (family.toRational E).lineP
    (family.integral E).Rq (family.rational E).Rq (family.toRational E).q.square
    (extendScalarChern (integralMap l E) (ProjectiveLine Y ↘ Y)
      ((family.toIntegral E).units Y) (family.toIntegral E).lineP family.zl.Rq
      (family.integral E).Rq (family.toIntegral E).q.square
      (realizeScalarChern l (ProjectiveLine Y ↘ Y) r.eP r.eY r.tq.Rc
        family.zl.Rq r.q_square a))
  let y := extendScalarChern (padicIntegersRingObjToContinuousMapRingObj l E)
    (secondProjection Y) ((family.toRational E).units (ProjectiveLine Y))
    (family.toRational E).lineW (family.integral E).R₂ (family.rational E).R₂
    (family.toRational E).p₂.square
    (extendScalarChern (integralMap l E) (secondProjection Y)
      ((family.toIntegral E).units (ProjectiveLine Y)) (family.toIntegral E).lineW
      family.zl.R₂ (family.integral E).R₂ (family.toIntegral E).p₂.square
      (realizeScalarChern l (secondProjection Y) r.eW r.eP r.t₂.Rc
        family.zl.R₂ r.p₂_square b))
  have hfinite :=
    scalar_chern_base_change_chern_some l E k p hpl Y δ family r a ha b hb
  unfold scalarQChern scalarP2Chern at hfinite
  dsimp only at hfinite
  let u := scalarUnitPullIso (coefficient l (some E)).X Y
  let j := secondDiagramPushIso _ Y _ (family.rational E)
  change (moduleObjectDerivedPullback (coefficient l (some E)).X
      (ProjectiveLine Y ↘ Y)).map
        (x ≫ (eqToIso (family.rational E).q_canonical).hom.app _) ≫
      secondTraceExchange l (some E) k p hpl Y = u.hom ≫ y ≫ j.hom.app _ at hfinite
  have hz : u.inv ≫
      (moduleObjectDerivedPullback (coefficient l (some E)).X
        (ProjectiveLine Y ↘ Y)).map
          (x ≫ (eqToIso (family.rational E).q_canonical).hom.app _) ≫
      secondTraceExchange l (some E) k p hpl Y ≫ j.inv.app _ = y := by
    exact remove_endpoint_isos u (j.app _) _ _ y hfinite
  have hclosure := closure_exchange_naturality l E k p hpl Y
    (family.rational E) family.closure (family.toClosure E) x
  unfold scalarQChern scalarP2Chern
  exact hclosure.trans (congrArg (fun v ↦
    (scalarUnitPullIso (coefficient l none).X Y).hom ≫
      extendScalarChern (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
        (secondProjection Y) ((family.toClosure E).units (ProjectiveLine Y))
        (family.toClosure E).lineW (family.rational E).R₂ family.closure.R₂
        (family.toClosure E).p₂.square v ≫
      (secondDiagramPushIso _ Y _ family.closure).hom.app _) hz)

end AlgebraicGeometry.ProEtale.RationalP1
