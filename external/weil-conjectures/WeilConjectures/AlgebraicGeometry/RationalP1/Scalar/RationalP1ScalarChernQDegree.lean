/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CompletedChernDegree

/-! # Trace one on the two transported Chern generators
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
open DiagonalCoefficients CondensedRing

attribute [local irreducible] singleUnitIso
attribute [local irreducible] moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square derivedScalars
attribute [local irreducible] Functor.mapDerivedCategory RestrictionSquare.mate
attribute [local irreducible] CompletedRealization.singleUnit CompletedRealization.shiftedLine

private theorem transport_degree
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V : C} {U' V' : D} (u : F.obj U ⟶ U') [IsIso u] (v : F.obj V ⟶ V')
    (c : U ⟶ V) (t : V ⟶ U) (t' : V' ⟶ U')
    (ht : F.map t ≫ u = v ≫ t') (hc : c ≫ t = 𝟙 _) :
    (inv u ≫ F.map c ≫ v) ≫ t' = 𝟙 _ := by
  simp only [Category.assoc]
  rw [← ht, ← F.map_comp_assoc, hc, F.map_id, Category.id_comp, IsIso.inv_hom_id]

private theorem degree_after_iso
    {C : Type*} [Category C] {U V W : C} (e : V ≅ W)
    (c : U ⟶ V) (t : V ⟶ U) (h : c ≫ t = 𝟙 _) :
    (c ≫ e.hom) ≫ e.inv ≫ t = 𝟙 _ := by
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h

private theorem realize_degree (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (r : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (s : CompletedPushSquare l f eX eS r.Rc R)
    (t : R.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X)) ⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (ht : CompletedTraceCompatibility l f eX eS r R s t)
    (a : DiagonalTrace.completedUnit l S ⟶
      r.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (ha : a ≫ r.trace = 𝟙 _) :
    realizeScalarChern l f eX eS r.Rc R s a ≫ t = 𝟙 _ := by
  let : IsIso (eS.singleUnit l S) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  unfold realizeScalarChern
  simpa only [Category.assoc] using transport_degree eS.F.mapDerivedCategory (eS.singleUnit l S)
    (s.derived.iso.hom.app _ ≫ R.R.map (eX.shiftedLine l X)) a r.trace t
    (by simpa only [CompletedTraceCompatibility, Category.assoc] using ht) ha

private theorem extend_degree
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (cL : Endpoint a M M' m)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (t : R.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧) ⟶
      unit Λ S)
    (t' : R'.R.obj (((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M') ⟦(2 : ℤ)⟧) ⟶
      unit Λ' S)
    (s : TraceCompatibility a f cU cL R R' t t')
    (c : unit Λ S ⟶ R.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧))
    (hc : c ≫ t = 𝟙 _) :
    extendScalarChern a f cU cL R R' s.square c ≫ t' = 𝟙 _ := by
  have hi : inv cU.iso.hom = cU.iso.inv :=
    IsIso.inv_eq_of_hom_inv_id cU.iso.hom_inv_id
  simpa only [extendScalarChern, Category.assoc, hi] using
    transport_degree (derivedScalars a S) cU.iso.hom
      ((s.square.mate a).app _ ≫ R'.R.map (cL.shift a)) c t t'
      (by simpa only [Category.assoc] using s.trace) hc

/-- The transported positive Chern adjunct of Q has normalized trace one. -/
theorem scalar_chern_q_degree
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (family : Family l Y) (r : Reference l Y δ family)
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a) :
    scalarQChern l c Y r a ≫
      trace (coefficient l c).X Y (line l c) (diagram l c Y family) = 𝟙 _ := by
  have hqa := completed_chern_degree l r.tq hY a
    ha
  have hzq := realize_degree l _ r.eP r.eY r.tq family.zl.Rq r.q_square
    family.zl.traceq r.q_trace a hqa
  have hiq (E : PadicAlgCl.FiniteIntermediateField l) :=
    extend_degree (integralMap l E) _ ((family.toIntegral E).units Y)
      (family.toIntegral E).lineP family.zl.Rq (family.integral E).Rq
      family.zl.traceq (family.integral E).traceq (family.toIntegral E).q _ hzq
  have hqq (E : PadicAlgCl.FiniteIntermediateField l) :=
    extend_degree (padicIntegersRingObjToContinuousMapRingObj l E) _
      ((family.toRational E).units Y) (family.toRational E).lineP
      (family.integral E).Rq (family.rational E).Rq
      (family.integral E).traceq (family.rational E).traceq (family.toRational E).q _ (hiq E)
  cases c with
  | some E =>
    unfold scalarQChern trace diagram line coefficient
    dsimp only
    exact degree_after_iso ((eqToIso (family.rational E).q_canonical).app _) _ _ (hqq E)
  | none =>
    have hq := extend_degree (Profinite.padicSubfieldRingObjToPadicAlgCl l (bottomField l)) _
      ((family.toClosure (bottomField l)).units Y) (family.toClosure (bottomField l)).lineP
      (family.rational (bottomField l)).Rq family.closure.Rq
      (family.rational (bottomField l)).traceq family.closure.traceq
      (family.toClosure (bottomField l)).q _ (hqq (bottomField l))
    unfold scalarQChern trace diagram line coefficient
    dsimp only
    exact degree_after_iso ((eqToIso family.closure.q_canonical).app _) _ _ hq

end AlgebraicGeometry.ProEtale.RationalP1
