/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectComparisonTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import all WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteDirectCounitFixedRealizationTransport
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicDirectImageUnitNormalization
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! The intrinsic conjugate before the final direct-image comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

section Transport
open CategoryTheory.Limits
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

private theorem transport_comp_square
    (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    (Lg : C₀ ⥤ C₁) (Lf : C₁ ⥤ C₂) (Lc : C₀ ⥤ C₂)
    (k : Lc ≅ Lg ⋙ Lf) (M : C₀) :
    e₂.functor.map (k.hom.app M) ≫
      (e₁.funInvIdAssoc (Lf ⋙ e₂.functor)).inv.app (Lg.obj M) ≫
      (e₁.inverse ⋙ Lf ⋙ e₂.functor).map
        ((e₀.funInvIdAssoc (Lg ⋙ e₁.functor)).inv.app M) =
    (e₀.funInvIdAssoc (Lc ⋙ e₂.functor)).inv.app M ≫
      (Functor.isoWhiskerLeft e₀.inverse (Functor.isoWhiskerRight k e₂.functor) ≪≫
        Functor.isoWhiskerLeft e₀.inverse
          (Functor.isoWhiskerRight
            (Functor.isoWhiskerLeft Lg (e₁.funInvIdAssoc Lf).symm) e₂.functor)).hom.app
              (e₀.functor.obj M) := by
  simp only [Equivalence.funInvIdAssoc_inv_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_map, Functor.comp_obj]
  simp only [← e₂.functor.map_comp, ← Lf.map_comp]
  have hn := e₁.unitIso.hom.naturality (Lg.map (e₀.unit.app M))
  change Lg.map (e₀.unit.app M) ≫ e₁.unit.app _ =
    e₁.unit.app _ ≫ e₁.inverse.map (e₁.functor.map (Lg.map (e₀.unit.app M))) at hn
  dsimp only [Functor.id_obj, Functor.comp_obj] at hn
  rw [← hn]
  simp only [Lf.map_comp, ← Category.assoc]
  have hk := k.hom.naturality (e₀.unit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hk
  rw [← hk]

private theorem mate_of_counit
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {Li : D₀ ⥤ D₁} {Ri : D₁ ⥤ D₀}
    (a : L ⊣ R) (ai : Li ⊣ Ri) (x : C₀ ⥤ D₀) (y : C₁ ⥤ D₁)
    (l : L ⋙ y ≅ x ⋙ Li) (b : R ⋙ x ⟶ y ⋙ Ri)
    (hc : ∀ N, y.map (a.counit.app N) =
      l.hom.app (R.obj N) ≫ Li.map (b.app N) ≫ ai.counit.app (y.obj N)) :
    (mateEquiv a ai (TwoSquare.mk _ _ _ _ l.inv)) = b := by
  ext N
  apply (ai.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit, hc]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem conjugate_square
    {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀}
    {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁}
    {Lc : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀}
    {Lgi : D₀ ⥤ D₁} {Rgi : D₁ ⥤ D₀}
    {Lfi : D₁ ⥤ D₂} {Rfi : D₂ ⥤ D₁}
    {Lci : D₀ ⥤ D₂} {Rci : D₂ ⥤ D₀}
    (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf) (ac : Lc ⊣ Rc)
    (agi : Lgi ⊣ Rgi) (afi : Lfi ⊣ Rfi) (aci : Lci ⊣ Rci)
    (x : C₀ ⥤ D₀) (y : C₁ ⥤ D₁) (z : C₂ ⥤ D₂)
    (lg : Lg ⋙ y ≅ x ⋙ Lgi) (lf : Lf ⋙ z ≅ y ⋙ Lfi)
    (lc : Lc ⋙ z ≅ x ⋙ Lci)
    (bg : Rg ⋙ x ⟶ y ⋙ Rgi) (bf : Rf ⋙ y ⟶ z ⋙ Rfi)
    (bc : Rc ⋙ x ⟶ z ⋙ Rci)
    (hg : (mateEquiv ag agi (TwoSquare.mk _ _ _ _ lg.inv)) = bg)
    (hf : (mateEquiv af afi (TwoSquare.mk _ _ _ _ lf.inv)) = bf)
    (hc : (mateEquiv ac aci (TwoSquare.mk _ _ _ _ lc.inv)) = bc)
    (k : Lc ≅ Lg ⋙ Lf) (ki : Lci ≅ Lgi ⋙ Lfi)
    (hk : ∀ M, z.map (k.hom.app M) ≫ lf.hom.app (Lg.obj M) ≫
      Lfi.map (lg.hom.app M) = lc.hom.app M ≫ ki.hom.app (x.obj M))
    (N : C₂) :
    x.map ((conjugateEquiv (ag.comp af) ac k.hom).app N) ≫ bc.app N =
      bg.app (Rf.obj N) ≫ Rgi.map (bf.app N) ≫
        (conjugateEquiv (agi.comp afi) aci ki.hom).app (z.obj N) := by
  let wg := TwoSquare.mk _ _ _ _ lg.inv
  let wf := TwoSquare.mk _ _ _ _ lf.inv
  let wc := TwoSquare.mk _ _ _ _ lc.inv
  have hs : wc.whiskerLeft k.hom =
      (TwoSquare.vComp wg wf).whiskerRight ki.hom := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    change lc.inv.app M ≫ z.map (k.hom.app M) =
      ki.hom.app (x.obj M) ≫ _
    apply (cancel_epi (lc.hom.app M)).mp
    apply (cancel_mono (lf.hom.app (Lg.obj M) ≫ Lfi.map (lg.hom.app M))).mp
    simpa only [TwoSquare.vComp, wg, wf,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc,
      Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
      ← Lfi.map_comp, Iso.inv_hom_id_app, Lfi.map_id] using hk M
  have h := mateEquiv_whiskerTop_conjugateEquiv (ag.comp af) ac
    (agi.comp afi) aci k.hom ki.hom (TwoSquare.vComp wg wf) wc hs
  have h' := congrArg (fun t ↦ t.app N) h
  rw [mateEquiv_hcomp] at h'
  simpa only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, wg, wf, wc, hg, hf, hc] using h'

end Transport

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  sfIntrinsicDerivedEquivalence

private theorem derived_realization_mate
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let EX := sfIntrinsicModuleEquivalence X A
    let EY := sfIntrinsicModuleEquivalence Y A
    let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    let l := (EY.funInvIdAssoc (L ⋙ EX.functor)).symm
    (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
        ).mapDerivedCategoryRightDerivedAdjunction
      (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso l).inv)) =
        (sfIntrinsicDerivedDirectImageComparison f A).inv := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Li := sfIntrinsicPullback A f
  let Ri := proEtaleConstantModuleDirectImage f A
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let adji := sfIntrinsicConstantModuleAdjunction f A
  let l := (EY.funInvIdAssoc (L ⋙ EX.functor)).symm
  let c := sfIntrinsicDirectImageComparison f A
  let b := sfIntrinsicDerivedDirectImageComparison f A
  have hc : ∀ N, EX.functor.map (adj.counit.app N) =
      l.hom.app (R.obj N) ≫ Li.map (c.inv.app N) ≫
        adji.counit.app (EX.functor.obj N) :=
    fun N ↦ conjugateRight_counit EY EX adj Ri c N
  exact mate_of_counit adj.mapDerivedCategoryRightDerivedAdjunction
    adji.mapDerivedCategoryRightDerivedAdjunction
    EY.functor.mapDerivedCategory EX.functor.mapDerivedCategory
    (Functor.mapDerivedCategorySquareIso l) b.inv
    (squareCounit R Ri EX.functor EY.functor L Li adj adji l c.symm hc b.symm
      (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A f))

private theorem derived_pullback_compositor_square
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory (Sheaf (ProEt.topology Z)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    let EX := sfIntrinsicModuleEquivalence X A
    let EY := sfIntrinsicModuleEquivalence Y A
    let EZ := sfIntrinsicModuleEquivalence Z A
    let Lf := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
    let Lg := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
    let Lc := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
    let lf := (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm
    let lg := (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm
    let lc := (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm
    EX.functor.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso
            (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) ≪≫
          (Functor.mapDerivedCategoryCompIso Lg Lf).symm).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso lf).hom.app (Lg.mapDerivedCategory.obj M) ≫
      (sfIntrinsicPullback A f).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso lg).hom.app M) =
      (Functor.mapDerivedCategorySquareIso lc).hom.app M ≫
        (sfIntrinsicDerivedPullbackComp A f g).hom.app
          (EZ.functor.mapDerivedCategory.obj M) := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let Lf := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let Lg := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
  let Lc := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
  let lf := (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm
  let lg := (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm
  let lc := (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm
  have hq (N) : EX.functor.map
      ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom.app N) ≫
      lf.hom.app (Lg.obj N) ≫ (sfIntrinsicPullback A f).map (lg.hom.app N) =
        lc.hom.app N ≫ (sfIntrinsicPullbackComp A f g).hom.app (EZ.functor.obj N) := by
    exact transport_comp_square EZ EY EX Lg Lf Lc
      (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) N
  have h := Functor.mapDerivedCategorySquareIso_comp Lg Lf Lc
    (sfIntrinsicPullback A g) (sfIntrinsicPullback A f) (sfIntrinsicPullback A (f ≫ g))
    EZ.functor EY.functor EX.functor lg lf lc
    (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g)
    (sfIntrinsicPullbackComp A f g) hq
  dsimp only [EX, EY, EZ, Lf, Lg, Lc, lf, lg, lc] at h
  dsimp only [sfIntrinsicPullback, sfIntrinsicTransport] at h ⊢
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Category.comp_id, Category.assoc,
    sfIntrinsicDerivedPullbackComp, sfIntrinsicPullback, sfIntrinsicTransport]
    using congrArg (fun t ↦ t.hom.app M) h

private theorem fixed_conjugate_exact
    (A : Type u) [CommRing A] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) g).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f))
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g).hom =
    conjugateEquiv
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) g
          ).mapDerivedCategoryRightDerivedAdjunction).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
          ).mapDerivedCategoryRightDerivedAdjunction)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) (f ≫ g)
        ).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} A)) f g) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).hom := by
  rw [exactProEtaleAdjunction_eq, exactProEtaleAdjunction_eq, exactProEtaleAdjunction_eq]
  ext K
  simp [conjugateEquiv_apply_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory]

/-
The final comparison isomorphism is cancellable, so this statement is one composition
shorter than the intrinsic-coordinate target.  Its proof is the left-derived/exact-derived
adjunction identification and the transported mate equation.
-/
theorem sfIntrinsicConjugateComparisonTransport
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    (conjugateIsoEquiv
        ((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction.comp
          (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction)
        (sfIntrinsicConstantModuleAdjunction (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
        (sfIntrinsicDerivedPullbackComp A f g)).hom.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I)) =
      sfIntrinsicAmbientCoordinate A f g I
          (leftDerivedUpperStarComp
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) ≫
      (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A).inv.app
        (DerivedCategory.Q.obj I) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let EX := sfIntrinsicModuleEquivalence X A
  let EY := sfIntrinsicModuleEquivalence Y A
  let EZ := sfIntrinsicModuleEquivalence Z A
  let Lf := upperStar B f
  let Lg := upperStar B g
  let Lc := upperStar B (f ≫ g)
  let af := (upperStarLowerStarAdjunction B f).mapDerivedCategoryRightDerivedAdjunction
  let ag := (upperStarLowerStarAdjunction B g).mapDerivedCategoryRightDerivedAdjunction
  let ac := (upperStarLowerStarAdjunction B (f ≫ g)).mapDerivedCategoryRightDerivedAdjunction
  let afi := (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
  let agi := (sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction
  let aci := (sfIntrinsicConstantModuleAdjunction (f ≫ g) A
    ).mapDerivedCategoryRightDerivedAdjunction
  let lf := Functor.mapDerivedCategorySquareIso (EY.funInvIdAssoc (Lf ⋙ EX.functor)).symm
  let lg := Functor.mapDerivedCategorySquareIso (EZ.funInvIdAssoc (Lg ⋙ EY.functor)).symm
  let lc := Functor.mapDerivedCategorySquareIso (EZ.funInvIdAssoc (Lc ⋙ EX.functor)).symm
  let cf := sfIntrinsicDerivedDirectImageComparison f A
  let cg := sfIntrinsicDerivedDirectImageComparison g A
  let cc := sfIntrinsicDerivedDirectImageComparison (f ≫ g) A
  let J := DerivedCategory.Q.obj I
  have h := conjugate_square ag af ac agi afi aci
    EZ.functor.mapDerivedCategory EY.functor.mapDerivedCategory EX.functor.mapDerivedCategory
    lg lf lc cg.inv cf.inv cc.inv
    (derived_realization_mate A g) (derived_realization_mate A f)
    (derived_realization_mate A (f ≫ g))
    (Functor.mapDerivedCategoryNatIso (upperStarComp B f g) ≪≫
      (Functor.mapDerivedCategoryCompIso Lg Lf).symm)
    (sfIntrinsicDerivedPullbackComp A f g)
    (derived_pullback_compositor_square A f g) J
  rw [← fixed_conjugate_exact A f g] at h
  have h' := congrArg (fun t ↦
    (proEtaleConstantDerivedDirectImage g A).map (cf.hom.app J) ≫
      cg.hom.app ((lowerStar B f).rightDerivedFunctor.obj J) ≫ t) h
  dsimp only [cf, cg, cc, J, agi, afi, aci, EX, EY, EZ] at h'
  simp only [Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at h'
  rw [(proEtaleConstantDerivedDirectImage g A).map_id, Category.id_comp] at h'
  rw [← sfIntrinsicDirectComparisonTransport A f g I
    (leftDerivedUpperStarComp B f g)]
  dsimp only [sfIntrinsicDerivedEquivalence, Equivalence.mapDerivedCategory,
    CategoryTheory.Equivalence.mk, proEtaleConstantDerivedDirectImage, conjugateIsoEquiv,
    Equiv.coe_fn_mk, Functor.comp_obj, B] at h' ⊢
  simpa only [Category.assoc] using h'.symm

end AlgebraicGeometry.Scheme
