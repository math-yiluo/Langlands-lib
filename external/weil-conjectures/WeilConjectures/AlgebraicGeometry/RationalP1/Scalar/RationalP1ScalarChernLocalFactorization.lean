/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.Scalar.RationalP1ScalarChernMaps
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLocalChernLift
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedModelChernAdjunct
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarRegularUnitPush
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalCanonicalUnitPush
import all WeilConjectures.AlgebraicGeometry.RationalP1.First.RationalP1FirstScalarTrace

/-! # Local classes underlying the scalar Chern adjuncts
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

/-- Whole-system normalization of a local completed section class. -/
def CompletedLocalChernNormalized (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (t : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧) : Prop :=
  (diagonalCompletedUnderlying l X).map z ≫
      DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l X)
        (t.restrictionX.F.mapDerivedCategory ⋙ t.LX.R)
        (t.coefficientsX.lineMap l (ULift.{u} (Padic l)) t.LX) 2 =
    t.coefficientsX.unitMap l (ULift.{u} (Padic l)) t.LX ≫
      t.LX.R.map (t.restrictionX.F.mapDerivedCategory.map
        (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) t.chernX
          (Scheme.Pic.mapHom t.model.model.hom (SpTowerClasses.hyperplanePic S))))

private theorem completed_local_chern_exists (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (hX : IsUnit (l : Γ(X, ⊤))) :
    ∃ z, CompletedLocalChernNormalized l p z := by
  simpa only [CompletedLocalChernNormalized, Scheme.Pic.mapHom_apply] using
    (DiagonalTrace.diagonalCompletedLocalChern_lift l p hX
      (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) p.chernX
        (Scheme.Pic.map p.model.model.hom (SpTowerClasses.hyperplanePic S)))).exists

/-- Realization of a local completed class, with no direct image. -/
@[irreducible]
def realizeLocalChern (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧) :
    unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) X ⟶
      ((DerivedCategory.singleFunctor
        (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
          (zlLine l X)) ⟦(2 : ℤ)⟧ :=
  letI : IsIso (e.singleUnit l X) := by
    unfold CompletedRealization.singleUnit
    infer_instance
  inv (e.singleUnit l X) ≫ e.F.mapDerivedCategory.map z ≫ e.shiftedLine l X

/-- Extend a local class through the specified unit and line endpoints. -/
@[irreducible]
def extendLocalChern
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u})
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (cU : Endpoint a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X))
    (cL : Endpoint a M M' m)
    (z : unit Λ X ⟶ ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧) :
    unit Λ' X ⟶ ((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M') ⟦(2 : ℤ)⟧ :=
  cU.iso.inv ≫ (derivedScalars a X).map z ≫ cL.shift a

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
  (Y : Scheme.{u})
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l (diagonalSurface Y)]
  {δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y}
  {family : Family l Y} (r : Reference l Y δ family)

/-- The two scalar extensions of the local class on the line. -/
@[irreducible]
def scalarQLocalChern
    (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      (DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧) :
    unit (coefficient l (some E)).X (ProjectiveLine Y) ⟶
      ((DerivedCategory.singleFunctor
        (Modules (coefficient l (some E)).X (ProjectiveLine Y)) 0).obj
          (line l (some E) (ProjectiveLine Y))) ⟦(2 : ℤ)⟧ :=
  extendLocalChern (padicIntegersRingObjToContinuousMapRingObj l E) _
    ((family.toRational E).units (ProjectiveLine Y)) (family.toRational E).lineP
    (extendLocalChern (integralMap l E) _
      ((family.toIntegral E).units (ProjectiveLine Y)) (family.toIntegral E).lineP
      (realizeLocalChern l _ r.eP z))

/-- The two scalar extensions of the local class on the product. -/
@[irreducible]
def scalarP2LocalChern
    (z : DiagonalTrace.completedUnit l (diagonalSurface Y) ⟶
      (DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧) :
    unit (coefficient l (some E)).X (diagonalSurface Y) ⟶
      ((DerivedCategory.singleFunctor
        (Modules (coefficient l (some E)).X (diagonalSurface Y)) 0).obj
          (line l (some E) (diagonalSurface Y))) ⟦(2 : ℤ)⟧ :=
  extendLocalChern (padicIntegersRingObjToContinuousMapRingObj l E) _
    ((family.toRational E).units (diagonalSurface Y)) (family.toRational E).lineW
    (extendLocalChern (integralMap l E) _
      ((family.toIntegral E).units (diagonalSurface Y)) (family.toIntegral E).lineW
      (realizeLocalChern l _ r.eW z))

/-- The coefficient-unit pullback comparison on the second projection. -/
@[irreducible]
def scalarP2UnitIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (moduleObjectDerivedPullback Λ (secondProjection Y)).obj
        (unit Λ (ProjectiveLine Y)) ≅ unit Λ (diagonalSurface Y) := by
  let F := moduleObjectDerivedPullback Λ (secondProjection Y)
  letI : F.Monoidal := by
    unfold F moduleObjectDerivedPullback internalMonoidal internalTensorBundle nativeTensorBundle
    exact monoidal_leftDerivedUpperStar Λ (secondProjection Y)
  exact F.mapIso (singleUnitIso Λ (ProjectiveLine Y)) ≪≫
    (Functor.Monoidal.εIso F).symm ≪≫ (singleUnitIso Λ (diagonalSurface Y)).symm

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor CondensedRing.upperStar CondensedRing.lowerStar
  derivedScalars CompletedRealization.singleUnit CompletedRealization.shiftedLine
set_option allowUnsafeReducibility true in
attribute [local reducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward
  derivedUpper derivedLower internalMonoidal internalTensorBundle nativeTensorBundle Mod.regular
attribute [local instance 21000] CondensedRing.monoidal_upperStar

private def regularUnitPush
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) :=
  (DerivedCategory.singleFunctor (Modules Λ S) 0).map
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv _ _
        (Functor.Monoidal.εIso (CondensedRing.upperStar Λ f)).inv) ≫
    singlePushComparison D (Mod.regular (condensedRingObj Λ X))

private theorem extend_local_adjunct
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (s : RestrictionSquare a f D D')
    (eS : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X))
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (eL : Endpoint a M M' m)
    (z : unit Λ X ⟶ ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧) :
    extendScalarChern a f eS eL D D' s (regularUnitPush Λ f D ≫ D.R.map z) =
      regularUnitPush Λ' f D' ≫ D'.R.map (extendLocalChern a X eX eL z) := by
  have hn := (s.mate a).naturality z
  dsimp only [Functor.comp_map] at hn
  have hu := scalar_regular_unit_push a f D D' s eS eX
  change (derivedScalars a S).map (regularUnitPush Λ f D) ≫
    (s.mate a).app (unit Λ X) ≫ D'.R.map eX.iso.hom =
      eS.iso.hom ≫ regularUnitPush Λ' f D' at hu
  unfold extendScalarChern extendLocalChern
  apply (cancel_epi eS.iso.hom).mp
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hu]
  simp only [← D'.R.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hn]

-- Transport a factorization by applying scalar extension to its equality.
private theorem extend_local_adjunct_of_eq
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (s : RestrictionSquare a f D D')
    (eS : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (eX : Endpoint a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X))
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (eL : Endpoint a M M' m)
    {c : unit Λ S ⟶ D.R.obj
      (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧)}
    {z : unit Λ X ⟶ ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ⟦(2 : ℤ)⟧}
    (hc : c = regularUnitPush Λ f D ≫ D.R.map z) :
    extendScalarChern a f eS eL D D' s c =
      regularUnitPush Λ' f D' ≫ D'.R.map (extendLocalChern a X eX eL z) :=
  (congrArg (extendScalarChern a f eS eL D D' s) hc).trans
    (extend_local_adjunct a f D D' s eS eX eL z)

private theorem unitEndpoint_nonempty
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    Nonempty (UnitPullEndpoint Λ f) := by
  exact ⟨nativeUnitPullEndpoint Λ f⟩

-- Realize the normalized adjunct before specializing the scheme and coefficient diagrams.
private theorem realize_local_regular_adjunct (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : DiagonalTrace.Presentation l (ULift.{u} (Padic l)) f)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (push : CompletedPushSquare l f eX eS p.Rc D)
    (b : DiagonalTrace.completedUnit l S ⟶
      p.Rc.R.obj ((DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l p b)
    (z : DiagonalTrace.completedUnit l X ⟶
      (DiagonalTrace.completedLine l X) ⟦(2 : ℤ)⟧)
    (hz : CompletedLocalChernNormalized l p z) :
    realizeScalarChern l f eX eS p.Rc D push b =
      regularUnitPush _ f D ≫ D.R.map (realizeLocalChern l X eX z) := by
  obtain ⟨cF⟩ := unitEndpoint_nonempty (Profinite.continuousMapRingObj.{u} ℤ_[l]) f
  have hlocal := diagonalCompletedModelChern_adjunct l f hS p eX eS D canonical
    hcanonical push cF b hb z (by
      simpa only [ModelLocalChernNormalized, CompletedLocalChernNormalized,
        Scheme.Pic.mapHom_apply] using hz)
  have hpush := diagonalCanonicalUnitPush l f D canonical hcanonical cF _
    (eX.localChern l X z)
  simpa only [realizeLocalChern, CompletedRealization.localChern, regularUnitPush]
    using hlocal.trans hpush.symm

-- Compare the native and bundled monoidal structures on the derived coefficient unit.
private theorem native_p2_endpoint
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (e : UnitPullEndpoint Λ (secondProjection Y)) :
    e.derived = (scalarP2UnitIso Λ Y).hom := by
  have he : e.iso.hom =
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (secondProjection Y))).inv := by
    apply ((CondensedRing.upperStarLowerStarAdjunction Λ (secondProjection Y)).homEquiv
      _ _).injective
    exact (ordinary_unit_endpoint Λ (secondProjection Y) e).symm
  unfold PullEndpoint.derived
  erw [he, singlePullback_unit]
  unfold scalarP2UnitIso
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [singleUnitIso_hom, singleUnitIso_inv]
  erw [(moduleObjectDerivedPullback Λ (secondProjection Y)).map_id]
  erw [Category.id_comp, Category.comp_id]
  unfold moduleObjectDerivedPullback internalMonoidal internalTensorBundle nativeTensorBundle
  rfl

-- Keep the canonical right-derived comparison generic in the coefficient ring.
private theorem canonical_local_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f)
    (hcanonical : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) D canonical)
    (cF : UnitPullEndpoint Λ f)
    (T : DerivedCategory (Modules Λ X)) (z : unit Λ X ⟶ T) :
    (regularUnitPush Λ f D ≫ D.R.map z) ≫ (eqToIso canonical).hom.app T =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _
        (cF.derived ≫ z) := by
  have h := canonical_unit_push_general Λ f D canonical hcanonical cF T z
  change regularUnitPush Λ f D ≫ D.R.map z =
    modelLocalAdjunct Λ f D canonical cF z at h
  rw [h]
  unfold modelLocalAdjunct
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

-- Identify any factored adjunct using its normalized unit pullback.
private theorem canonical_local_adjunct_of_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (canonical : D.R = derivedLower Λ f)
    (hcanonical : IsCanonicalRightDerived (CondensedRing.lowerStar Λ f) D canonical)
    (u : (derivedUpper Λ f).obj (unit Λ S) ⟶ unit Λ X)
    (hu : ∀ cF : UnitPullEndpoint Λ f, cF.derived = u)
    {T : DerivedCategory (Modules Λ X)} {z : unit Λ X ⟶ T}
    {c : unit Λ S ⟶ D.R.obj T} (hc : c = regularUnitPush Λ f D ≫ D.R.map z) :
    c ≫ (eqToIso canonical).hom.app T =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ (u ≫ z) := by
  obtain ⟨cF⟩ := unitEndpoint_nonempty Λ f
  refine (hc =≫ (eqToIso canonical).hom.app T).trans
    ((canonical_local_adjunct Λ f D canonical hcanonical cF T z).trans ?_)
  exact congrArg ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv
    (unit Λ S) T) (hu cF =≫ z)

-- Compare the canonical adjunct and the monoidal endpoint before specializing coefficients.
private theorem canonical_q_local_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)))
    (canonical : D.R = derivedLower Λ (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y)) D canonical)
    (T : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (z : unit Λ (ProjectiveLine Y) ⟶ T) :
    (regularUnitPush Λ (ProjectiveLine Y ↘ Y) D ≫ D.R.map z) ≫
        (eqToIso canonical).hom.app T =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
        (ProjectiveLine Y ↘ Y)).homEquiv _ _ ((scalarUnitPullIso Λ Y).hom ≫ z) := by
  let cF := nativeUnitPullEndpoint Λ (ProjectiveLine Y ↘ Y)
  rw [canonical_local_adjunct Λ _ D canonical hcanonical cF]
  rw [unitPullEndpoint_eq Λ Y cF]

-- Compare the canonical adjunct and the monoidal endpoint before specializing coefficients.
private theorem canonical_p2_local_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (D : DiagonalRightDerived (CondensedRing.lowerStar Λ (secondProjection Y)))
    (canonical : D.R = derivedLower Λ (secondProjection Y))
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar Λ (secondProjection Y)) D canonical)
    (T : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (z : unit Λ (diagonalSurface Y) ⟶ T) :
    (regularUnitPush Λ (secondProjection Y) D ≫ D.R.map z) ≫
        (eqToIso canonical).hom.app T =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ
        (secondProjection Y)).homEquiv _ _ ((scalarP2UnitIso Λ Y).hom ≫ z) := by
  let cF := nativeUnitPullEndpoint Λ (secondProjection Y)
  refine (canonical_local_adjunct Λ _ D canonical hcanonical cF T z).trans ?_
  exact congrArg (fun e : (derivedUpper Λ (secondProjection Y)).obj
      (unit Λ (ProjectiveLine Y)) ⟶ unit Λ (diagonalSurface Y) ↦
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (secondProjection Y)).homEquiv
      (unit Λ (ProjectiveLine Y)) T (e ≫ z)) (native_p2_endpoint Λ Y cF)

-- Concrete coefficient conversions cross the named derived functor interfaces.
/-- A normalized completed adjunct comes from its local section class, and this
factorization survives realization and both finite-field scalar changes. -/
theorem scalar_chern_local_factorization
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (a : DiagonalTrace.completedUnit l Y ⟶
      r.tq.Rc.R.obj ((DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧))
    (ha : CompletedChernNormalized l r.tq.toPresentation a)
    (b : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
      r.t₂.Rc.R.obj ((DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧))
    (hb : CompletedChernNormalized l r.t₂.toPresentation b) :
    ∃ (z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
          (DiagonalTrace.completedLine l (ProjectiveLine Y)) ⟦(2 : ℤ)⟧)
      (w : DiagonalTrace.completedUnit l (diagonalSurface Y) ⟶
          (DiagonalTrace.completedLine l (diagonalSurface Y)) ⟦(2 : ℤ)⟧),
      CompletedLocalChernNormalized l r.tq.toPresentation z ∧
      CompletedLocalChernNormalized l r.t₂.toPresentation w ∧
      scalarQChern l (some E) Y r a =
        (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient l (some E)).X
          (ProjectiveLine Y ↘ Y)).homEquiv _ _
          ((scalarUnitPullIso (coefficient l (some E)).X Y).hom ≫
            scalarQLocalChern l E Y r z) ∧
      scalarP2Chern l (some E) Y r b =
        (CondensedRing.derivedUpperStarLowerStarAdjunction (coefficient l (some E)).X
          (secondProjection Y)).homEquiv _ _
          ((scalarP2UnitIso (coefficient l (some E)).X Y).hom ≫
            scalarP2LocalChern l E Y r w) := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using hP.map (secondProjection Y).appTop.hom
  -- Keep witness selection independent of the full factorization proposition.
  have ez := completed_local_chern_exists l r.tq.toPresentation hP
  have ew := completed_local_chern_exists l r.t₂.toPresentation hW
  let z := ez.choose
  let w := ew.choose
  have hz := ez.choose_spec
  have hw := ew.choose_spec
  refine ⟨z, w, hz, hw, ?_, ?_⟩
  · have hreal := realize_local_regular_adjunct l (ProjectiveLine Y ↘ Y) hY r.tq.toPresentation
      r.eP r.eY family.zl.Rq family.zl.q_canonical family.zl.q_unit r.q_square a ha z hz
    have hi := extend_local_adjunct_of_eq (integralMap l E) (ProjectiveLine Y ↘ Y) family.zl.Rq
      (family.integral E).Rq (family.toIntegral E).q.square
      ((family.toIntegral E).units Y) ((family.toIntegral E).units (ProjectiveLine Y))
      (family.toIntegral E).lineP hreal
    have hq := extend_local_adjunct_of_eq (padicIntegersRingObjToContinuousMapRingObj l E)
      (ProjectiveLine Y ↘ Y) (family.integral E).Rq (family.rational E).Rq
      (family.toRational E).q.square
      ((family.toRational E).units Y) ((family.toRational E).units (ProjectiveLine Y))
      (family.toRational E).lineP hi
    have hfinal := canonical_local_adjunct_of_eq
      (Profinite.continuousMapRingObj.{u} E.1) (ProjectiveLine Y ↘ Y)
      (family.rational E).Rq (family.rational E).q_canonical (family.rational E).q_unit
      (scalarUnitPullIso _ Y).hom (unitPullEndpoint_eq _ Y) hq
    simpa only [scalarQChern, scalarQLocalChern, coefficient, line] using hfinal
  · have hreal := realize_local_regular_adjunct l (secondProjection Y) hP r.t₂.toPresentation
      r.eW r.eP family.zl.R₂ family.zl.p₂_canonical family.zl.p₂_unit r.p₂_square b hb w hw
    have hi := extend_local_adjunct_of_eq (integralMap l E) (secondProjection Y) family.zl.R₂
      (family.integral E).R₂ (family.toIntegral E).p₂.square
      ((family.toIntegral E).units (ProjectiveLine Y))
      ((family.toIntegral E).units (diagonalSurface Y)) (family.toIntegral E).lineW hreal
    have hq := extend_local_adjunct_of_eq (padicIntegersRingObjToContinuousMapRingObj l E)
      (secondProjection Y) (family.integral E).R₂ (family.rational E).R₂
      (family.toRational E).p₂.square
      ((family.toRational E).units (ProjectiveLine Y))
      ((family.toRational E).units (diagonalSurface Y)) (family.toRational E).lineW hi
    have hfinal := canonical_local_adjunct_of_eq
      (Profinite.continuousMapRingObj.{u} E.1) (secondProjection Y)
      (family.rational E).R₂ (family.rational E).p₂_canonical (family.rational E).p₂_unit
      (scalarP2UnitIso _ Y).hom (native_p2_endpoint _ Y) hq
    -- Reduce the identity wrappers in the named pushforward comparison explicitly.
    unfold scalarP2Chern scalarP2LocalChern secondDiagramPushIso
    dsimp only
    simpa only [coefficient, line, secondProjection, diagonalSurface, Modules, id_eq,
      moduleObjectDerivedPushforward, derivedLower] using hfinal

end AlgebraicGeometry.ProEtale.RationalP1
