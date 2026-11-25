/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPositiveUnitSquare
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteSplitting

/-! # The components of the twisted projective-line splitting

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private lemma derived_inverse_triangle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (Y : DerivedCategory C) :
    e.functor.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso e.functor e.inverse).hom.app Y) ≫
          (Functor.mapDerivedCategoryNatIso e.unitIso.symm).hom.app Y ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app Y) =
      (Functor.mapDerivedCategoryCompIso e.inverse e.functor).hom.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (e.functor.mapDerivedCategory.obj Y) := by
  have h := Functor.mapDerivedCategoryCompNatIso_cocycle
    e.unitIso.symm (Iso.refl e.functor) e.counitIso (Iso.refl e.functor)
    (fun X ↦ by simpa using (e.counit_app_functor X).symm) Y
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, NatTrans.comp_app] at h
  have hl := congr_app (Functor.mapDerivedCategoryCompIso_id_comp e.functor) Y
  have hr := congr_app (Functor.mapDerivedCategoryCompIso_comp_id e.functor) Y
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hl hr
  have hl' : (Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).hom.app Y =
      e.functor.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app Y) := by
    exact ((Iso.inv_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).app Y)).mp hl).symm
  have hr' : (Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).hom.app Y =
      (Functor.mapDerivedCategoryIdIso D).hom.app
        (e.functor.mapDerivedCategory.obj Y) := by
    exact ((Iso.inv_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).app Y)).mp hr).symm
  rw [hl', hr'] at h
  apply (cancel_mono ((Functor.mapDerivedCategoryNatIso (Iso.refl e.functor)).hom.app Y)).mp
  simpa only [Functor.map_comp, Category.assoc] using h

private lemma retwist_shift
    {C : Type*} [Category C] [HasShift C ℤ]
    (F : C ⥤ C) [F.CommShift ℤ] {I Y : C} (k : I ⟶ Y⟦(2 : ℤ)⟧) :
    (F.map (k⟦(-2 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C (2 : ℤ) (-2) (by decide)).hom.app Y))⟦(2 : ℤ)⟧' =
      ((F.commShiftIso (-2 : ℤ)).hom.app I)⟦(2 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C (-2 : ℤ) 2 (by decide)).hom.app (F.obj I) ≫
        F.map k ≫ (F.commShiftIso (2 : ℤ)).hom.app Y := by
  rw [F.map_comp, F.map_shiftFunctorCompIsoId_hom_app]
  have hn := (F.commShiftIso (-2 : ℤ)).hom.naturality k
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [shift_shiftFunctorCompIsoId_hom_app]
  simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
    Functor.map_comp, Category.assoc]
    using congrArg (((F.commShiftIso (-2 : ℤ)).hom.app I)⟦(2 : ℤ)⟧' ≫ ·)
    ((shiftFunctorCompIsoId C (-2 : ℤ) 2 (by decide)).hom.naturality
      (F.map k ≫ (F.commShiftIso (2 : ℤ)).hom.app Y))

private lemma retwist_inverse
    {C : Type*} [Category C] [HasShift C ℤ]
    (F N : C ⥤ C) [F.CommShift ℤ]
    (γ : F ⋙ N ≅ 𝟭 C) (δ : N ⋙ F ≅ 𝟭 C)
    (htriangle : ∀ Y, F.map (γ.hom.app Y) = δ.hom.app (F.obj Y))
    {U I Y Z : C} (i : N.obj U ≅ I) (w : (F.obj Y)⟦(2 : ℤ)⟧ ≅ Z)
    (c : U ⟶ Z) :
    let b := (shiftFunctor C (2 : ℤ)).mapIso ((F.commShiftIso (-2 : ℤ)).app I) ≪≫
      (shiftFunctorCompIsoId C (-2 : ℤ) 2 (by decide)).app (F.obj I) ≪≫
      F.mapIso i.symm ≪≫ δ.app U
    let k := i.inv ≫ N.map (c ≫ w.inv ≫ (F.commShiftIso (2 : ℤ)).inv.app Y) ≫
      γ.hom.app (Y⟦(2 : ℤ)⟧)
    c = b.inv ≫
      (F.map (k⟦(-2 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C (2 : ℤ) (-2) (by decide)).hom.app Y))⟦(2 : ℤ)⟧' ≫
      w.hom := by
  let b := (shiftFunctor C (2 : ℤ)).mapIso ((F.commShiftIso (-2 : ℤ)).app I) ≪≫
    (shiftFunctorCompIsoId C (-2 : ℤ) 2 (by decide)).app (F.obj I) ≪≫
    F.mapIso i.symm ≪≫ δ.app U
  change c = b.inv ≫ _
  apply (cancel_epi b.hom).mp
  rw [Iso.hom_inv_id_assoc]
  rw [retwist_shift]
  simp only [b, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Category.assoc]
  congr 2
  have hn := δ.hom.naturality
    (c ≫ w.inv ≫ (F.commShiftIso (2 : ℤ)).inv.app Y)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hn
  rw [F.map_comp, F.map_comp, htriangle]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (N.map _)), hn]
  simp only [Functor.id_obj, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [w.inv_hom_id, Category.comp_id]

private lemma projection_mate_unit
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    (T : C ⥤ C) (V : D ⥤ D) (α : T ⋙ L ≅ L ⋙ V)
    {U : C} {W : D} (q : L.obj U ⟶ W) :
    T.map (adj.homEquiv U W q) ≫
        adj.homEquiv _ _ (α.hom.app (R.obj W) ≫ V.map (adj.counit.app W)) =
      adj.homEquiv _ _ (α.hom.app U ≫ V.map q) := by
  rw [← adj.homEquiv_naturality_left]
  congr 1
  have hn := α.hom.naturality (adj.homEquiv U W q)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← V.map_comp]
  have hq : L.map (adj.homEquiv U W q) ≫ adj.counit.app W = q := by
    simpa only [Adjunction.homEquiv_counit] using
      (adj.homEquiv U W).symm_apply_apply q
  rw [hq]

private lemma adjoint_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (L : C ⥤ D) (R : D ⥤ C) (adj : L ⊣ R)
    [L.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ]
    {U : C} {W : D} (q : L.obj U ⟶ W) :
    adj.homEquiv _ _ ((L.commShiftIso (2 : ℤ)).hom.app U ≫ q⟦(2 : ℤ)⟧') =
      (adj.homEquiv U W q)⟦(2 : ℤ)⟧' ≫ (R.commShiftIso (2 : ℤ)).inv.app W := by
  rw [← cancel_mono ((R.commShiftIso (2 : ℤ)).hom.app W)]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app]
  have hn := (R.commShiftIso (2 : ℤ)).hom.naturality q
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  have hu := adj.unit_app_commShiftIso_hom_app ℤ (2 : ℤ) U
  simp only [Functor.commShiftIso_comp_hom_app] at hu
  simpa only [Functor.comp_obj, Functor.id_obj, Category.comp_id, Category.assoc]
    using congrArg (· ≫ (R.map q)⟦(2 : ℤ)⟧') hu

/-- Evaluation makes the unit/Chern splitting invertible, and its positive twist
has the geometric twisted unit and Chern adjunct as its two components.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), the unit/Chern
isomorphism and twisting before second projection.
(blueprint: lem-sfb-diagonal-trace-twisted-splitting-components).

Proof: the normalized integral Chern construction evaluates to the finite Kummer
Chern class of the pullback of O(1). The hyperplane section has positive Cartier
normalization, so the finite projective-line decomposition says that each evaluation
of bq is invertible. This holds on the specified model by transport along its
isomorphism with P1. No assertion that evaluation detects arbitrary equalities of
derived morphisms is needed.
For the first component, the projection map is the counit mate of the positive-line
pullback. Apply its defining mate equation and the adjunction triangle identities
to the coefficient unit. The section normalizations of coefficient pullback,
line pullback and positive pullback identify this with the geometric twisted unit;
the positive-unit comparison supplies a. For the second component, substitute the
definition of Model.second as the negative twist of the Chern adjunct. Positive
and negative twists cancel by the tensor/Hom evaluation and coevaluation identities.
Naturality of their shift comparisons cancels shifts -2 and 2, with b the resulting
contraction. Thus the two displayed equations hold in the derived category of
systems itself. They are equations before taking the inverse splitting and do not
assume bq invertible or state a trace normalization. -/
theorem diagonalTrace_twistedSplitting_components
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    let E := ULift.{u} (Padic l)
    let T := p.twistS.T l E ⋙ shiftFunctor (D S (Arings l E S)) (2 : ℤ)
    let a := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
      (p.twistS.positiveUnit l E).symm
    let b := (shiftFunctor (D S (Arings l E S)) (2 : ℤ)).mapIso
        (((p.twistS.T l E).commShiftIso (-2 : ℤ)).app (inverseLine l E p.chernS)) ≪≫
      (shiftFunctorCompIsoId (D S (Arings l E S)) (-2 : ℤ) 2 (by decide)).app
        ((p.twistS.T l E).obj (inverseLine l E p.chernS)) ≪≫
      p.twistS.contract l E
    (∀ n : ℕ, IsIso ((SpTowerShriek.Ev l E S n).map (p.model.bq l E))) ∧
      p.model.twistedUnit l E =
        a.hom ≫ T.map biprod.inl ≫ T.map (p.model.bq l E) ≫
          (p.model.twistedPush l E).hom ∧
      p.model.chernAdjoint l E =
        b.inv ≫ T.map biprod.inr ≫ T.map (p.model.bq l E) ≫
          (p.model.twistedPush l E).hom := by
  let E := ULift.{u} (Padic l)
  let m := p.model
  let L : D S (Arings l E S) ⥤ D X (Arings l E X) := SpTowerShriek.pull l E p.base m.geometry
  let R : D X (Arings l E X) ⥤ D S (Arings l E S) := SpTowerShriek.push l E p.base m.geometry
  let adj : L ⊣ R := SpTowerShriek.adjunction l E p.base m.geometry
  let F := p.twistS.T l E
  let N := p.twistS.N l E
  let V := p.twistX.T l E
  let α := m.positivePullback.derivedIso l E
  let q := (m.coefficientPullback.derivedIso l E).hom
  let r := (m.linePullback.derivedIso l E).hom
  let ps := p.twistS.positiveUnit l E
  let px := p.twistX.positiveUnit l E
  let : m.geometry.pull.Additive := m.geometry.pullAdditive
  let : m.geometry.push.Additive := m.geometry.pushAdditive
  let : PreservesFiniteLimits m.geometry.pull := m.geometry.pullLimits
  let : PreservesFiniteColimits m.geometry.pull := m.geometry.pullColimits
  let : HasKInjectiveResolutions (Systems X (Arings l E X)) := p.base.kinjective X
  let : adj.CommShift ℤ :=
    CategoryTheory.canonicalRightDerivedAdjunctionShift
      (C := Systems S (Arings l E S)) (D := Systems X (Arings l E X))
      m.geometry.ordinaryAdjunction
  refine ⟨diagonalTrace_finite_splitting l p hS, ?_, ?_⟩
  · have hu : adj.homEquiv _ _ r = ps.inv ≫ F.map (unitArrow l E m.coefficientPullback) ≫
        projection l E m.geometry m.positivePullback (unit X (Arings l E X)) ≫
          R.map px.hom := by
      apply (cancel_epi ps.hom).mp
      simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← adj.homEquiv_naturality_left]
      change adj.homEquiv _ _ (L.map ps.hom ≫ r) = _
      rw [positivePullback_unit_square l E m.geometry m.coefficientPullback
        m.linePullback m.positivePullback]
      change adj.homEquiv _ _ (α.hom.app _ ≫ V.map q ≫ px.hom) = _
      rw [← Category.assoc, adj.homEquiv_naturality_right]
      congr 1
      exact (projection_mate_unit L R adj F V α q).symm
    change m.twistedUnit l E =
      ((shiftFunctor _ (2 : ℤ)).mapIso ps.symm).hom ≫
        (F ⋙ shiftFunctor _ (2 : ℤ)).map biprod.inl ≫
        (F ⋙ shiftFunctor _ (2 : ℤ)).map (m.bq l E) ≫ (m.twistedPush l E).hom
    rw [← Functor.map_comp_assoc, Model.bq, biprod.inl_desc]
    change adj.homEquiv _ _
        ((L.commShiftIso (2 : ℤ)).hom.app _ ≫ r⟦(2 : ℤ)⟧') = _
    rw [adjoint_shift L R adj r, hu]
    simp only [Model.twistedPush, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Iso.app_hom, Functor.comp_map, Functor.map_comp, Category.assoc,
      asIso_hom]
    rfl
  · let γ := p.twistS.cancelNegative l E
    let δ : N ⋙ F ≅ 𝟭 (D S (Arings l E S)) :=
      Functor.mapDerivedCategoryCompIso p.twistS.equivalence.inverse
        p.twistS.equivalence.functor ≪≫
      Functor.mapDerivedCategoryNatIso p.twistS.equivalence.counitIso ≪≫
      Functor.mapDerivedCategoryIdIso (Systems S (Arings l E S))
    have htriangle (Y : D S (Arings l E S)) :
        F.map (γ.hom.app Y) = δ.hom.app (F.obj Y) := by
      simpa only [γ, δ, Twisting.cancelNegative, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app] using derived_inverse_triangle p.twistS.equivalence Y
    have hc := retwist_inverse F N γ δ htriangle (p.twistS.inverseUnit l E)
      (m.twistedPush l E) (m.chernAdjoint l E)
    change m.chernAdjoint l E = _
    rw [← Functor.map_comp_assoc, Model.bq, biprod.inr_desc]
    simpa only [Model.second, Twisting.contract, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_hom, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.comp_map, NatTrans.comp_app, δ,
      Category.assoc] using hc

end AlgebraicGeometry.ProEtale.DiagonalTrace
