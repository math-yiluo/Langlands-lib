/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerChernTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerAdjunctTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChern
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree

/-! # Finite normalization of the completed positive Chern adjunct

Source: diagonal tower coefficient changes proof (1), and trace proof (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit

private theorem complete_rightAdjoint
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R) (l : ℕ) (M : D)
    (hM : ∀ V : D, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M)) :
    ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ R.obj M) := by
  intro V hV
  have : IsIso (l • 𝟙 (L.obj V)) := by
    have he : L.map (l • 𝟙 V) = l • 𝟙 (L.obj V) :=
      (L.map_nsmul).trans (congrArg (fun a ↦ l • a) (L.map_id V))
    rw [← he]
    exact L.map_isIso (l • 𝟙 V)
  have := hM (L.obj V) inferInstance
  exact (adj.homEquiv V M).symm.injective.subsingleton

private theorem completed_local_lift
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y)
    (theta : SpTowerClasses.unit (ProjectiveLine Y)
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (ProjectiveLine Y)) ⟶
      (SpTowerClasses.line l (ULift.{u} (Padic l)) s.tq.chernX)⟦(2 : ℤ)⟧) :
    ∃ z : DiagonalTrace.completedUnit l (ProjectiveLine Y) ⟶
        (DiagonalTrace.completedLine l (ProjectiveLine Y))⟦(2 : ℤ)⟧,
      (diagonalCompletedUnderlying l (ProjectiveLine Y)).map z ≫
          DiagonalTrace.shiftedComparison (diagonalCompletedUnderlying l (ProjectiveLine Y))
            (s.tq.restrictionX.F.mapDerivedCategory ⋙ s.tq.LX.R)
            (s.tq.coefficientsX.lineMap l (ULift.{u} (Padic l)) s.tq.LX) 2 =
        s.tq.coefficientsX.unitMap l (ULift.{u} (Padic l)) s.tq.LX ≫
          s.tq.LX.R.map (s.tq.restrictionX.F.mapDerivedCategory.map theta) := by
  let X := ProjectiveLine Y
  let F := diagonalCompletedUnderlying l X
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l X)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l X),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  have hY : IsUnit (l : Γ(Y, ⊤)) := by
    apply isUnit_pow_succ_iff.mp
    simpa only [Nat.cast_pow] using s.hYpow
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  let inst : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  let U := SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))
  have hunit := DiagonalTrace.diagonalCompletedLine_complete l X U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  have hfree : (Scheme.purTwistZlModule X l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X l (ULift.{u} (Padic l))).2.1.2.1
  have hline := DiagonalTrace.diagonalCompletedLine_complete l X _ hfree
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l X)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l X)) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adjShift l
    (F.obj (DiagonalTrace.completedLine l X)) hline
  have htarget : P ((DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      ((F.commShiftIso (2 : ℤ)).app (DiagonalTrace.completedLine l X))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let A : P.FullSubcategory := ⟨DiagonalTrace.completedUnit l X, hunit⟩
  let B : P.FullSubcategory := ⟨(DiagonalTrace.completedLine l X)⟦(2 : ℤ)⟧, htarget⟩
  let v := DiagonalTrace.shiftedComparison F
    (s.tq.restrictionX.F.mapDerivedCategory ⋙ s.tq.LX.R)
    (s.tq.coefficientsX.lineMap l (ULift.{u} (Padic l)) s.tq.LX) 2
  have : IsIso v := by
    have := s.tq.line_limit
    dsimp only [v, DiagonalTrace.shiftedComparison]
    infer_instance
  obtain ⟨ff⟩ := DiagonalTrace.diagonalCompleteScalarRestrictionCore l X
  obtain ⟨z, hz⟩ := ff.map_surjective (X := A) (Y := B)
    (s.tq.coefficientsX.unitMap l (ULift.{u} (Padic l)) s.tq.LX ≫
      s.tq.LX.R.map (s.tq.restrictionX.F.mapDerivedCategory.map theta) ≫ inv v)
  change F.map z.hom = _ at hz
  refine ⟨z.hom, ?_⟩
  exact (congrArg (fun k ↦ k ≫ v) hz).trans (by
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id])

private theorem comparison_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (F : C ⥤ C') (G : D ⥤ D')
    (p : F ⋙ L' ≅ L ⋙ G) {M : C} {N : D} (f : L.obj M ⟶ N) :
    F.map ((ad.homEquiv _ _) f) ≫
        (ad'.homEquiv _ _) (p.hom.app (R.obj N) ≫ G.map (ad.counit.app N)) =
      (ad'.homEquiv _ _) (p.hom.app M ≫ G.map f) := by
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  have hn : L'.map (F.map ((ad.homEquiv _ _) f)) ≫ p.hom.app (R.obj N) =
      p.hom.app M ≫ G.map (L.map ((ad.homEquiv _ _) f)) :=
    p.hom.naturality ((ad.homEquiv _ _) f)
  rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
  have h : L.map ((ad.homEquiv _ _) f) ≫ ad.counit.app N = f :=
    (ad.homEquiv _ _).symm_apply_apply f
  rw [h]

private theorem ordinary_positive_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)).homEquiv _ _
        ((geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom ≫
          (geoP1Comparison A (ProjectiveLine Y)).map (geoP1EtaleChern A N hN hA Y hY)) =
      biprod.inr ≫ geoP1TwistedMap A N hN hA Y hY := by
  let d := Etale.projectiveLineTraceDatum N hN A hA Y hY
  symm
  simp only [geoP1TwistedMap, geoP1SumComparison, biprod.inr_desc_assoc,
    ← Functor.map_comp_assoc]
  rw [d.decomposition_hom, biprod.inr_desc]
  unfold Etale.ordinaryFiniteP1ChernPushforward geoP1PushComparison
  have h := comparison_adjunct
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
    (geoP1Comparison A Y) (geoP1Comparison A (ProjectiveLine Y))
    (geoP1PullComparison A (ProjectiveLine Y ↘ Y))
    ((Etale.ordinaryFiniteUnitPullback A (ProjectiveLine Y ↘ Y)).hom ≫ d.chern)
  refine h.trans ?_
  congr 1
  simp only [geoP1UnitPullback, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rfl

private theorem ordinary_positive_adjunct_of_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    {k : geoP1Unit A (ProjectiveLine Y) ⟶ geoP1Twist A N hA (ProjectiveLine Y) 1 2}
    (hk : k = (geoP1Comparison A (ProjectiveLine Y)).map
      (geoP1EtaleChern A N hN hA Y hY)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)).homEquiv _ _
        ((geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom ≫ k) =
      biprod.inr ≫ geoP1TwistedMap A N hN hA Y hY := by
  subst k
  exact ordinary_positive_adjunct A N hN hA Y hY

private theorem commutes_of_transport_eq
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    {B R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj B] [IsCommMonObj B] [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {N : ℕ} {hN : 0 < N} {hA : (N : A) = 0} {hY : IsUnit (N : Γ(Y, ⊤))}
    (x : ChernCoefficientDiagram l Y B R A N hN hA hY)
    {w : geoP1Unit A Y ⟶ (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
      (geoP1Twist A N hA (ProjectiveLine Y) 1 2)}
    (hw : w = biprod.inr ≫ geoP1TwistedMap A N hN hA Y hY)
    (h : x.TransportTo l Y x.c w) : x.Commutes := by
  subst w
  unfold ChernCoefficientDiagram.TransportTo at h
  unfold ChernCoefficientDiagram.Commutes
  exact h

attribute [local irreducible] Scheme.finiteEtaleTateLine Etale.ordinaryFiniteDegreeZero

/-- The completed positive Chern adjunct becomes the finite positive Chern adjunct.

Source: blueprint latest, diagonal tower coefficient changes proof (1), the finite
coefficient reduction, and trace proof (1), the class of the positive section.
(blueprint: lem-diagonal-uniformizer-chern-normalization).

Proof: the normalization hc expresses c as the completed lift of the strict-system
Chern adjunct. Compare its coefficient and root cones with the finite projections.
The coefficient-one equations of tq and completedY identify the coefficient cone
with the actual unit reduction. The integral-root projection equations in lineP,
and its finite kernel inclusion, identify the line cone with the positive Kummer
root map, without a scalar or sign ambiguity. Compute the boundary on the same
K-flat resolution of the integral line-bundle extension and tensor it with the
finite quotient. The map from Z/l^(n+1) exists by hA. Coefficient naturality of the
Kummer boundary identifies this reduced class with the finite Kummer class of
O(1), because q_model is the identity. Adjunction transports the class to its
Chern adjunct. The ordinary underlying-sheaf normalization and the full derived
unit equations identify this adjunct transport with the four prescribed
pushforward comparisons in v. The equality q_canonical and its hcanonical
normalization fix the final canonical finite pushforward. The fourStepChernCommutes
predicate composes precisely
these four unit and pushforward comparisons. This gives equality of Chern arrows
before any trace is composed. Neither q_trace nor a Chern/trace degree equation is used.
The exponent n+1 is positive even at n=0; hA handles ramification, and the
construction also applies to the empty scheme. -/
theorem diagonalUniformizer_chernNormalization
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    (s : UniformizerChernNormalizationData l Y) :
    s.ChernNormalized l Y := by
  let theta := SpTowerClasses.firstChern l (ULift.{u} (Padic l)) s.tq.chernX
    (SpTowerClasses.hyperplanePic Y)
  obtain ⟨z, hz⟩ := completed_local_lift l Y s theta
  have hz' : s.LocalNormalized l Y theta z := by
    unfold UniformizerChernNormalizationData.LocalNormalized
    exact hz
  have hc' : s.AdjunctNormalized l Y s.c := by
    unfold UniformizerChernNormalizationData.AdjunctNormalized
    exact s.hc
  let p : NormalizedAdjunctPair l Y s :=
    { z := z
      c := s.c
      local_normalized := hz'
      adjunct_normalized := hc' }
  have h := diagonalUniformizer_adjunctTransport l Y s p
  unfold NormalizedAdjunctPair.Transported at h
  dsimp only [p] at h
  have hLocal := s.localChern l Y z hz'
  unfold UniformizerChernNormalizationData.LocalChernNormalized at hLocal
  have hEq := ordinary_positive_adjunct_of_eq
    (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) s.hA Y s.hYpow hLocal
  change (s.diagram l Y).TransportTo l Y (s.diagram l Y).c _ at h
  -- Reuse the diagram's parameters, including its coefficient instances.
  open Lean Elab Tactic in
  run_tac do
    withMainContext do
      let ctx ← getLCtx
      let some hd := ctx.findFromUserName? `h | throwError "Missing transport proof"
      let some ed := ctx.findFromUserName? `hEq | throwError "Missing finite adjunct equality"
      let ht ← Meta.inferType hd.toExpr
      unless ht.isAppOfArity ``ChernCoefficientDiagram.TransportTo 23 do
        throwError "Unexpected transport predicate"
      let x := ht.getAppArgs[20]!
      let xt ← Meta.inferType x
      unless xt.isAppOfArity ``ChernCoefficientDiagram 20 do
        throwError "Unexpected coefficient diagram"
      let helper := mkConst ``commutes_of_transport_eq xt.getAppFn.constLevels!
      let proof := mkAppN helper
        (xt.getAppArgs ++ #[x, ht.getAppArgs[22]!, ed.toExpr, hd.toExpr])
      Meta.withTransparency .all <| closeMainGoal `coefficient_transport proof

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
