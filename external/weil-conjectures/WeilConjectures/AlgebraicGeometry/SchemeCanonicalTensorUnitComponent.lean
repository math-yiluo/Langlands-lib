/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeTensorUnitAction
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation

/-! # The canonical coefficient formula for a tensor-unit action
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem tensor_unit_summand {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C]
    [HasColimitsOfSize.{0, 0} C] (F : CochainComplex C ℤ) (p : ℤ) :
    HomologicalComplex.ιMapBifunctor F (HomologicalComplex.tensorUnit C (.up ℤ))
        (curriedTensor C) (.up ℤ) p 0 p (add_zero p) ≫
        (HomologicalComplex.rightUnitor F).hom.f p =
      F.X p ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom ≫
        (ρ_ (F.X p)).hom := by
  apply (cancel_mono ((HomologicalComplex.rightUnitor F).inv.f p)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.comp_id]
  change _ = _ ≫ _ ≫ (HomologicalComplex.rightUnitor' F).inv p
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  exact (Category.id_comp _).symm

private theorem tensor_action_summand {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C]
    [HasColimitsOfSize.{0, 0} C] (F V P N : CochainComplex C ℤ)
    (e : HomologicalComplex.tensorObj V P ⟶ N)
    (p q r n s k : ℤ) (hpq : p + q = n) (hnr : n + r = k)
    (hqr : q + r = s) (hps : p + s = k) :
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor C) (.up ℤ) p q n hpq ▷ P.X r) ≫
      HomologicalComplex.ιMapBifunctor (HomologicalComplex.tensorObj F V) P
        (curriedTensor C) (.up ℤ) n r k hnr ≫
        ((HomologicalComplex.associator F V P).hom ≫
          HomologicalComplex.mapBifunctorMap (𝟙 F) e (curriedTensor C) (.up ℤ)).f k =
      (α_ (F.X p) (V.X q) (P.X r)).hom ≫
        F.X p ◁ (HomologicalComplex.ιMapBifunctor V P (curriedTensor C) (.up ℤ)
          q r s hqr ≫ e.f s) ≫
        HomologicalComplex.ιMapBifunctor F N (curriedTensor C) (.up ℤ) p s k hps := by
  have hi := HomologicalComplex.mapBifunctor₁₂.ι_eq
    (curriedTensor C) (curriedTensor C) F V P (.up ℤ) (.up ℤ)
      p q r n k hpq hnr
  simp only [curriedTensor_map_app] at hi
  simp only [HomologicalComplex.comp_f, ← Category.assoc]
  rw [← hi]
  simp only [Category.assoc]
  change (HomologicalComplex.mapBifunctor₁₂.ι _ _ F V P _ _ p q r k _) ≫
    (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso C)
      F V P (.up ℤ) (.up ℤ) (.up ℤ) k).hom ≫ _ = _
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (curriedTensor C) (curriedTensor C) F V P (.up ℤ) (.up ℤ) (.up ℤ)
      p q r s k hqr hps]
  simp only [curriedTensor_obj_map, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap, HomologicalComplex.id_f,
    curriedTensor_map_app, curriedTensor_obj_map, id_whiskerRight,
    whiskerLeft_comp]
  dsimp only [curriedAssociatorNatIso, bifunctorComp₁₂, bifunctorComp₂₃, curriedTensor]
  simp only [Category.id_comp]
  rfl

private theorem tensor_unit_action_component {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]
    (F V P : CochainComplex C ℤ)
    (e : HomologicalComplex.tensorObj V P ⟶ HomologicalComplex.tensorUnit C (.up ℤ))
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor C) (.up ℤ) p q n hpq ▷ P.X r) ≫
      HomologicalComplex.ιMapBifunctor (HomologicalComplex.tensorObj F V) P
        (curriedTensor C) (.up ℤ) n r k hnr ≫
        ((HomologicalComplex.associator F V P).hom ≫
          HomologicalComplex.mapBifunctorMap (𝟙 F) e (curriedTensor C) (.up ℤ) ≫
            (HomologicalComplex.rightUnitor F).hom).f k =
      if h : r + q = 0 then
        (α_ (F.X p) (V.X q) (P.X r)).hom ≫
          F.X p ◁ (HomologicalComplex.ιMapBifunctor V P (curriedTensor C) (.up ℤ)
            q r 0 (by change q + r = 0; omega) ≫ e.f 0 ≫
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).hom) ≫
          (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = k)).hom
      else 0 := by
  classical
  by_cases h : r + q = 0
  · rw [dite_eq_left h]
    have hpk : p = k := by omega
    cases hpk
    have ht := tensor_action_summand F V P _ e p q r n 0 p hpq hnr
      (by omega) (add_zero p)
    have ht' := congrArg (fun t ↦ t ≫ (HomologicalComplex.rightUnitor F).hom.f p) ht
    simp only [HomologicalComplex.comp_f, Category.assoc] at ht'
    simp only [HomologicalComplex.comp_f]
    rw [ht', tensor_unit_summand]
    simp only [whiskerLeft_comp, Category.assoc, HomologicalComplex.XIsoOfEq,
      eqToIso_refl, Iso.refl_hom, Category.comp_id]
  · rw [dite_eq_right h]
    have ht := tensor_action_summand F V P _ e p q r n (q + r) k hpq hnr rfl (by omega)
    have ht' := congrArg (fun t ↦ t ≫ (HomologicalComplex.rightUnitor F).hom.f k) ht
    simp only [HomologicalComplex.comp_f, Category.assoc] at ht'
    simp only [HomologicalComplex.comp_f]
    rw [ht']
    have hz : HomologicalComplex.ιMapBifunctor V P (curriedTensor C) (.up ℤ)
        q r (q + r) rfl ≫ e.f (q + r) = 0 :=
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) (q + r)
        (by omega)).eq_of_tgt _ _
    rw [hz]
    simp

private theorem uncurry_postcomp {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (A H B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (π : H ⟶ SheafOfModules.homObj A B) (g : B ⟶ B') :
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.symmetricCategory R
    (β_ H A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A H B).symm π ≫ g =
      (β_ H A).hom ≫ (SheafOfModules.tensorHomEquiv (R := R) A H B').symm
        (π ≫ SheafOfModules.homObjMap (R := R) (𝟙 A) g) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  congr 1
  apply (SheafOfModules.tensorHomEquiv (R := R) A H B').injective
  simp only [SheafOfModules.tensorHomEquiv_comp_homObjMap, Equiv.apply_symm_apply]

private theorem evaluation_summand_postcomp (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q r n : ℤ) (h : r + q = n)
    (B : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (g : N.X n ⟶ B) :
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    HomologicalComplex.ιMapBifunctor (homComplex (R := Y.sheaf) P N) P
        (curriedTensor _) (.up ℤ) q r n (by change q + r = n; omega) ≫
          schemeOrdinaryEvaluationGraded Y P N n ≫ g =
      (β_ ((homComplex (R := Y.sheaf) P N).X q) (P.X r)).hom ≫
        (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r)
          ((homComplex (R := Y.sheaf) P N).X q) B).symm
          (π P N q r n h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r)) g) := by
  intro π
  simp only [← Category.assoc]
  unfold schemeOrdinaryEvaluationGraded
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only [schemeOrdinaryEvaluationGradedComponent]
  simp only [Category.assoc]
  exact uncurry_postcomp Y.sheaf (P.X r) _ (N.X n) B (π P N q r n h) g

set_option backward.isDefEq.respectTransparency.types true in
/-- A tensor-unit action has the canonical dual-projection component formula.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation chain calculation, coefficient cancellation and tensor action.
(blueprint: lem-pc-scheme-canonical-tensor-unit-component).

Proof: Restrict the assumed factorization to V^q tensor P^r. The component
formula for schemeTensorHomUncurry and coefficient naturality of the Hom
projections give the uncurried old projection followed by eta_O. The
augmentation is degreewise monic: monoQuasiIso_toKInjectiveResolution_app
makes it monic as a chain map, and evaluation preserves finite limits.
Cancel it to determine the component of e. For r+q=0, postcompose this
component with singleObjXSelf and use tensor-Hom coefficient naturality to
move this identification inside uncurrying. Restrict the total tensor action
to (F^p tensor V^q) tensor P^r: the total associator acts by the component
associator without a sign, and tensor-map naturality gives the component of e.
The single-unit right unitor is the coefficient identification followed by
rho and XIsoOfEq; the degree equations give p=k. Thus the displayed formula
holds when r+q=0. Otherwise O^(r+q) is zero, so the tensor action component
vanishes. Finally postcompose with eta_F; the component of a composition is
the composition of components. No ordinary evaluation map f, no ordinary
component predicate, no boundedness or flatness, and no existence of e are
used. Zero maps, zero complexes, negative degrees and the empty scheme are
included by the same argument. -/
theorem schemeCanonicalTensorUnit_component (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (e : pullbackTensorTotal Y
      (homComplex (R := Y.sheaf) P
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) P ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    schemeTensorHomUncurry Y V P O
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)) =
        e ≫ eta.app O →
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorUnitAction Y F V P e ≫ eta.app F).f k =
    (if h : r + q = 0 then
      (α_ (F.X p) (V.X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ (V.X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (V.X q)
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).symm
              (π P O q r 0 h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = k)).hom
    else 0) ≫ (eta.app F).f k := by
  classical
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  intro O V eta π hO
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let := SheafOfModules.monoidalClosed (R := Y.sheaf)
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  have : Mono (eta.app O) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ O).1
  have he (j : ℤ) : e.f j = schemeOrdinaryEvaluationGraded Y P O j := by
    apply (cancel_mono ((eta.app O).f j)).1
    have hh := congrArg (fun f ↦ f.f j) hO
    change (schemeTensorHomUncurry Y V P O
      (((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O))).f j =
        e.f j ≫ (eta.app O).f j at hh
    rw [schemeOrdinaryEvaluationGraded_augmentation] at hh
    exact hh.symm
  have hcoeff (h : r + q = 0) := evaluation_summand_postcomp Y P O q r 0 h
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom
  have ha := tensor_unit_action_component F V P e p q r n k hpq hnr
  have ha' := congrArg (fun t ↦ t ≫ (eta.app F).f k) ha
  simp only [schemeTensorUnitAction, HomologicalComplex.comp_f, Category.assoc] at ⊢
  simp only [HomologicalComplex.comp_f, Category.assoc] at ha'
  apply ha'.trans
  apply congrArg (fun t ↦ t ≫ (eta.app F).f k)
  split_ifs with h
  · simp only [he 0]
    rw [hcoeff h]
  · rfl

end AlgebraicGeometry
