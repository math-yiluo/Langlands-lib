/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeOpenImmersion
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData

/-! # The intrinsic realization of the open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint

open CategoryTheory.Functor CategoryTheory.Limits

private theorem comparison_unit
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (F : D ≌ D')
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R')
    (q : R' ⋙ E.inverse ≅ F.inverse ⋙ R)
    (r : F.functor ⋙ R' ≅ R ⋙ E.functor)
    (hq : ∀ M, R.map (F.unitIso.hom.app M) ≫ q.inv.app (F.functor.obj M) =
      E.unitIso.hom.app (R.obj M) ≫ E.inverse.map (r.inv.app M))
    (K : C) :
    E.functor.map (a.unit.app K) ≫ r.inv.app (L.obj K) =
      b.unit.app (E.functor.obj K) ≫ R'.map
        ((((E.toAdjunction.comp b).ofNatIsoRight q).leftAdjointUniq
          (a.comp F.toAdjunction)).hom.app K) := by
  let s := ((E.toAdjunction.comp b).ofNatIsoRight q).leftAdjointUniq
    (a.comp F.toAdjunction)
  have hs := Adjunction.unit_leftAdjointUniq_hom_app
    ((E.toAdjunction.comp b).ofNatIsoRight q) (a.comp F.toAdjunction) K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, whiskerLeft_app, Functor.comp_map, Category.assoc] at hs
  change E.unitIso.hom.app K ≫ E.inverse.map (b.unit.app (E.functor.obj K)) ≫
    q.hom.app (L'.obj (E.functor.obj K)) ≫ R.map (F.inverse.map (s.hom.app K)) =
    a.unit.app K ≫ R.map (F.unitIso.hom.app (L.obj K)) at hs
  apply E.inverse.map_injective
  apply (cancel_epi (E.unitIso.hom.app K)).mp
  apply (cancel_mono (q.hom.app (F.functor.obj (L.obj K)))).mp
  simp only [Functor.map_comp, Category.assoc]
  have hn := E.unitIso.hom.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← Category.assoc (E.unitIso.hom.app (R.obj (L.obj K))), ← hq]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  have hqn := q.hom.naturality (s.hom.app K)
  dsimp only [Functor.comp_map] at hqn
  erw [Category.comp_id, hqn]
  exact hs.symm

private theorem mate_eq_of_unit
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') {E : C ⥤ C'} {F : D ⥤ D'}
    (s : E ⋙ L' ⟶ L ⋙ F) (r : R ⋙ E ⟶ F ⋙ R')
    (h : ∀ K, E.map (a.unit.app K) ≫ r.app (L.obj K) =
      b.unit.app (E.obj K) ≫ R'.map (s.app K)) :
    (mateEquiv a b s) = r := by
  have hs : s = ((mateEquiv a b).symm r) := by
    ext K
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit]
    exact (h K).symm.trans (unit_mateEquiv_symm a b r K)
  rw [hs]
  exact ((mateEquiv a b).apply_symm_apply r)

private theorem inverse_mate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (a : L ⊣ R) (b : L' ⊣ R') {P : C ⥤ E} {Q : D ⥤ F}
    (r : R ⋙ P ⟶ Q ⋙ R') (K : C) :
    ((mateEquiv a b).symm r).app K =
      (b.homEquiv _ _).symm (P.map (a.unit.app K) ≫ r.app (L.obj K)) := by
  apply (b.homEquiv _ _).injective
  change (b.homEquiv (P.obj K) (Q.obj (L.obj K)))
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).app K) =
      (b.homEquiv (P.obj K) (Q.obj (L.obj K)))
        ((b.homEquiv (P.obj K) (Q.obj (L.obj K))).symm _)
  rw [(b.homEquiv (P.obj K) (Q.obj (L.obj K))).apply_symm_apply,
    Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r) K).symm

private theorem scalar_mate_cube
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    (EA : C ≌ C') (EB : D ≌ D') (EC : E ≌ E') (ED : F ≌ F')
    {L : C ⥤ D} {R : D ⥤ C} {Lz : E ⥤ F} {Rz : F ⥤ E}
    {L' : C' ⥤ D'} {R' : D' ⥤ C'} {Lz' : E' ⥤ F'} {Rz' : F' ⥤ E'}
    (a : L ⊣ R) (b : Lz ⊣ Rz) (a' : L' ⊣ R') (b' : Lz' ⊣ Rz')
    (s : EA.functor ⋙ L' ≅ L ⋙ EB.functor)
    (sz : EC.functor ⋙ Lz' ≅ Lz ⋙ ED.functor)
    (r : EB.functor ⋙ R' ≅ R ⋙ EA.functor)
    (rz : ED.functor ⋙ Rz' ≅ Rz ⋙ EC.functor)
    (hs : ∀ K, EA.functor.map (a.unit.app K) ≫ r.inv.app (L.obj K) =
      a'.unit.app (EA.functor.obj K) ≫ R'.map (s.hom.app K))
    (hsz : ∀ K, EC.functor.map (b.unit.app K) ≫ rz.inv.app (Lz.obj K) =
      b'.unit.app (EC.functor.obj K) ≫ Rz'.map (sz.hom.app K))
    {JA : C ⥤ E} {JB : D ⥤ F} {IA : C' ⥤ E'} {IB : D' ⥤ F'}
    (eA : EA.functor ⋙ IA ≅ JA ⋙ EC.functor)
    (eB : EB.functor ⋙ IB ≅ JB ⋙ ED.functor)
    (q : R ⋙ JA ⟶ JB ⋙ Rz) (q' : R' ⋙ IA ⟶ IB ⋙ Rz')
    (hq : ∀ N, IA.map (r.hom.app N) ≫ eA.hom.app (R.obj N) ≫
      EC.functor.map (q.app N) =
        q'.app (EB.functor.obj N) ≫ Rz'.map (eB.hom.app N) ≫ rz.hom.app (JB.obj N))
    (K : C) :
    ((mateEquiv a' b').symm q').app (EA.functor.obj K) ≫
        IB.map (s.hom.app K) =
      Lz'.map (eA.hom.app K) ≫ sz.hom.app (JA.obj K) ≫
        ED.functor.map (((mateEquiv a b).symm q).app K) ≫
          eB.inv.app (L.obj K) := by
  have hright (N : D) :
      eA.inv.app (R.obj N) ≫ IA.map (r.inv.app N) ≫ q'.app (EB.functor.obj N) =
      EC.functor.map (q.app N) ≫ rz.inv.app (JB.obj N) ≫ Rz'.map (eB.inv.app N) := by
    have h := congrArg (fun t ↦ eA.inv.app (R.obj N) ≫ IA.map (r.inv.app N) ≫
      t ≫ rz.inv.app (JB.obj N) ≫ Rz'.map (eB.inv.app N)) (hq N)
    simp only [Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc] at h
    erw [IA.map_id] at h
    simp only [Category.id_comp, Iso.inv_hom_id_app_assoc] at h
    rw [← Rz'.map_comp, Iso.hom_inv_id_app] at h
    erw [Rz'.map_id, Category.comp_id] at h
    exact h.symm
  have h := (equivalenceAdjunctionComparison_inverseMate EA EB EC ED a b a' b'
    r.symm rz.symm s.symm sz.symm
    (mate_eq_of_unit a a' s.hom r.inv hs)
    (mate_eq_of_unit b b' sz.hom rz.inv hsz)
    JA JB IA IB eA.symm eB.symm q q' hright).1 K
  have ht := congrArg (fun t ↦ Lz'.map (eA.hom.app K) ≫ sz.hom.app (JA.obj K) ≫
    t ≫ IB.map (s.hom.app K)) h
  simp only [Iso.symm_hom, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc] at ht
  erw [Lz'.map_id, IB.map_id] at ht
  erw [Category.comp_id] at ht
  simpa only [Category.id_comp] using ht.symm

private theorem conjugated_open_cube
    {C D C' D' E F E' F' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Category E] [Category F] [Category E'] [Category F']
    (EXA : C ≌ C') (EXB : D ≌ D') (EZA : E ≌ E') (EZB : F ≌ F')
    (RX : D ⥤ C) (RZ : F ⥤ E) (RX' : D' ⥤ C') (RZ' : F' ⥤ E')
    (JA : C ⥤ E) (JB : D ⥤ F)
    (rX : EXB.functor ⋙ RX' ≅ RX ⋙ EXA.functor)
    (rZ : EZB.functor ⋙ RZ' ≅ RZ ⋙ EZA.functor)
    (qX : RX' ⋙ EXA.inverse ≅ EXB.inverse ⋙ RX)
    (q : RX ⋙ JA ≅ JB ⋙ RZ)
    (hX : ∀ M, qX.hom.app (EXB.functor.obj M) ≫ RX.map (EXB.unitIso.inv.app M) =
      EXA.inverse.map (rX.hom.app M) ≫ EXA.unitIso.inv.app (RX.obj M))
    (M : D) :
    (EXA.inverse ⋙ JA ⋙ EZA.functor).map (rX.hom.app M) ≫
        (EXA.funInvIdAssoc (JA ⋙ EZA.functor)).hom.app (RX.obj M) ≫
        EZA.functor.map (q.hom.app M) =
      (isoWhiskerRight qX (JA ⋙ EZA.functor) ≪≫
        isoWhiskerLeft EXB.inverse (isoWhiskerRight q EZA.functor) ≪≫
        isoWhiskerLeft (EXB.inverse ⋙ JB) rZ.symm).hom.app (EXB.functor.obj M) ≫
      RZ'.map ((EXB.funInvIdAssoc (JB ⋙ EZB.functor)).hom.app M) ≫
        rZ.hom.app (JB.obj M) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Equivalence.funInvIdAssoc_hom_app, Functor.comp_map, Functor.comp_obj, Category.assoc]
  have hn := rZ.inv.naturality (JB.map (EXB.unitIso.inv.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  have hq := q.hom.naturality (EXB.unitIso.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hq
  simp only [← EZA.functor.map_comp]
  apply EZA.functor.congr_map
  rw [← hq]
  simp only [← JA.map_comp_assoc]
  rw [hX]
  rfl

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

attribute [local irreducible] sfIntrinsicModuleEquivalence

private theorem realization_functor (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).functor =
      (sfIntrinsicModuleEquivalence T A).functor.mapDerivedCategory := rfl

private theorem realization_inverse (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).inverse =
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory := rfl

private theorem realization_adjunction (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    (sfIntrinsicDerivedEquivalence T A).toAdjunction =
      (sfIntrinsicModuleEquivalence T A).toAdjunction.mapDerivedCategoryAdjunction := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro H
  rw [Adjunction.mapDerivedCategoryAdjunction_counit_app_Qh_obj]
  change ((mapDerivedCategoryCompIso _ _).hom ≫
    (mapDerivedCategoryNatIso (sfIntrinsicModuleEquivalence T A).counitIso).hom ≫
      (mapDerivedCategoryIdIso _).hom).app (DerivedCategory.Qh.obj H) = _
  simp only [NatTrans.comp_app]
  rw [mapDerivedCategoryIdIso_hom_app_Qh_obj, mapDerivedCategoryNatIso_fach]
  rw [← mapDerivedCategoryCompIso_hom_app_factorsh]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  congr 2
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  congr 1

/-- The mate of the forward realization restriction comparison is the inverse realization
restriction comparison. -/
private theorem forward_realization_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B) :
    mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
        (sfIntrinsicModuleEquivalence T A).toAdjunction
        (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) =
      TwoSquare.mk _ _ _ _ (sfInverseRealizationRestriction T φ).inv := by
  have h {C D E F : Type (u + 2)}
      [Category.{u + 1} C] [Category.{u + 1} D] [Category.{u + 1} E] [Category.{u + 1} F]
      (eC : C ≌ E) (eD : D ≌ F) (G : C ⥤ D) (H : E ⥤ F)
      (e : eC.functor ⋙ H ≅ G ⋙ eD.functor) :
      mateEquiv eC.toAdjunction eD.toAdjunction e.inv =
        (isoWhiskerRight eC.counitIso.symm (H ⋙ eD.inverse) ≪≫
          isoWhiskerLeft eC.inverse (isoWhiskerRight e eD.inverse) ≪≫
          isoWhiskerLeft (eC.inverse ⋙ G) eD.unitIso.symm).inv := by
    apply NatTrans.ext
    funext M
    simp [mateEquiv_apply, Equivalence.toAdjunction, Equivalence.unit, Equivalence.counit,
      Category.assoc]
  exact h (sfIntrinsicModuleEquivalence T B) (sfIntrinsicModuleEquivalence T A)
    (sfFixedRestriction T φ) (proEtaleCoefficientRestrictScalars T φ)
    (sfRealizationRestriction T φ)

private theorem inverse_realization_unit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (sfFixedRestriction T φ).map ((sfIntrinsicModuleEquivalence T B).unitIso.hom.app M) ≫
        (sfInverseRealizationRestriction T φ).inv.app
          ((sfIntrinsicModuleEquivalence T B).functor.obj M) =
      (sfIntrinsicModuleEquivalence T A).unitIso.hom.app
          ((sfFixedRestriction T φ).obj M) ≫
        (sfIntrinsicModuleEquivalence T A).inverse.map
          ((sfRealizationRestriction T φ).inv.app M) := by
  have h := unit_mateEquiv (sfIntrinsicModuleEquivalence T B).toAdjunction
    (sfIntrinsicModuleEquivalence T A).toAdjunction
    (TwoSquare.mk _ _ _ _ (sfRealizationRestriction T φ).inv) M
  rw [forward_realization_mate] at h
  exact h

private theorem inverse_realization_inverse_unit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :
    (sfInverseRealizationRestriction T φ).hom.app
          ((sfIntrinsicModuleEquivalence T B).functor.obj M) ≫
        (sfFixedRestriction T φ).map ((sfIntrinsicModuleEquivalence T B).unitIso.inv.app M) =
      (sfIntrinsicModuleEquivalence T A).inverse.map
          ((sfRealizationRestriction T φ).hom.app M) ≫
        (sfIntrinsicModuleEquivalence T A).unitIso.inv.app
          ((sfFixedRestriction T φ).obj M) := by
  have h :
      (sfFixedRestriction T φ).mapIso ((sfIntrinsicModuleEquivalence T B).unitIso.app M) ≪≫
        ((sfInverseRealizationRestriction T φ).app
          ((sfIntrinsicModuleEquivalence T B).functor.obj M)).symm =
      (sfIntrinsicModuleEquivalence T A).unitIso.app ((sfFixedRestriction T φ).obj M) ≪≫
        (sfIntrinsicModuleEquivalence T A).inverse.mapIso
          ((sfRealizationRestriction T φ).app M).symm :=
    Iso.ext (inverse_realization_unit T φ M)
  exact congrArg Iso.inv h

private theorem realization_scalar_unit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (T : Scheme.{u}) (φ : A →+* B)
    (K : DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedEquivalence T A).functor.map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift)).unit.app K) ≫
      (mapDerivedCategorySquareIso (sfRealizationRestriction T φ)).inv.app
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology T) φ.ulift).obj K) =
    (pbcDerivedScalarAdjunction (scalarRingMap φ T)).unit.app
        ((sfIntrinsicDerivedEquivalence T A).functor.obj K) ≫
      (pbcDerivedRestrict (scalarRingMap φ T)).map
        ((realizationScalarIso φ T).hom.app K) := by
  let EA := sfIntrinsicDerivedEquivalence T A
  let EB := sfIntrinsicDerivedEquivalence T B
  let q := mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  let r := mapDerivedCategorySquareIso (sfRealizationRestriction T φ)
  have hq : ∀ M,
      (Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift).map
          (EB.unitIso.hom.app M) ≫ q.inv.app (EB.functor.obj M) =
        EA.unitIso.hom.app
            ((Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift).obj M) ≫
          EA.inverse.map (r.inv.app M) := by
    intro M
    have hM := Adjunction.mapDerivedCategoryAdjunction_mate
      (sfIntrinsicModuleEquivalence T B).toAdjunction
      (sfIntrinsicModuleEquivalence T A).toAdjunction
      (sfInverseRealizationRestriction T φ).symm
      (sfRealizationRestriction T φ).symm
      (fun N ↦ (inverse_realization_unit T φ N).symm) M
    rw [← realization_adjunction T A, ← realization_adjunction T B] at hM
    simp only [Equivalence.toAdjunction_unit, Equivalence.unit] at hM
    simpa only [CategoryTheory.Functor.square_symm_hom, EA, EB, q, r,
      sfFixedRestriction, Sheaf.derivedRestrictScalars, Sheaf.restrictScalars,
      realization_functor, realization_inverse, Functor.comp_obj, Functor.id_obj] using hM.symm
  have h := comparison_unit EA EB
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology T) φ.ulift))
    (pbcDerivedScalarAdjunction (scalarRingMap φ T)) q r hq K
  simp only [realizationScalarIso, EA, EB, q, r, ProEtale.pbcFixedScalarExtension,
    pbcDerivedRestrict, pbcRestrict, scalarRingMap, proEtaleConstantRingMap,
    proEtaleCoefficientRestrictScalars, sfFixedRestriction, Sheaf.derivedRestrictScalars,
    Sheaf.restrictScalars, realization_functor, realization_inverse,
    Functor.comp_obj, Functor.id_obj] at h ⊢
  convert h using 1
  congr 4

private theorem realization_restriction_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
        ((mapDerivedCategorySquareIso (sfRealizationRestriction X φ)).hom.app K) ≫
      (openRealizationIso A j).hom.app
        ((Sheaf.derivedRestrictScalars (ProEt.topology X) φ.ulift).obj K) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom.app K) =
    (mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom.app
        ((sfIntrinsicDerivedEquivalence X B).functor.obj K) ≫
      (pbcDerivedRestrict (scalarRingMap φ Z)).map ((openRealizationIso B j).hom.app K) ≫
      (mapDerivedCategorySquareIso (sfRealizationRestriction Z φ)).hom.app
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.obj K) := by
  apply Etale.mapDerivedCategorySquareIso_hom_app_comp_of_comm
    (sfRealizationRestriction X φ)
    ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence Z A).functor))
    ((sfIntrinsicModuleEquivalence X B).funInvIdAssoc
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
          (sfIntrinsicModuleEquivalence Z B).functor))
    (sfRealizationRestriction Z φ) (sfFixedOpenRestriction j φ) (sfOpenRestriction j φ)
  intro M
  exact conjugated_open_cube
    (sfIntrinsicModuleEquivalence X A) (sfIntrinsicModuleEquivalence X B)
    (sfIntrinsicModuleEquivalence Z A) (sfIntrinsicModuleEquivalence Z B)
    (sfFixedRestriction X φ) (sfFixedRestriction Z φ)
    (proEtaleCoefficientRestrictScalars X φ) (proEtaleCoefficientRestrictScalars Z φ)
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
    (sfRealizationRestriction X φ) (sfRealizationRestriction Z φ)
    (sfInverseRealizationRestriction X φ) (sfFixedOpenRestriction j φ)
    (inverse_realization_inverse_unit X φ) M

/-- Intrinsic realization preserves the fixed-coefficient open scalar mate.

Source: Stacks Tags 03DI and 00YV; the realization part of Step 2 of
lem-finite-open-scalar-transport.
(blueprint: lem-finite-open-scalar-realization-transport).

Proof: conjugate the open/coefficient restriction square by the canonical
realization equivalences at X and Z. Its value is sfOpenRestriction by its
definition. The coefficient comparisons are sfRealizationRestriction and its
inverse-equivalence conjugate, and the open comparison is the equivalence unit.
More explicitly, this conjugation first applies the inverse-realization
restriction square at X, then the fixed open restriction square, then the
inverse forward-realization square at Z, all whiskered by the inverse realization
at X and the forward realization at Z. Inserting the open comparison cancels
the adjacent forward/inverse realization pair. The inverse-realization square
is itself the forward square conjugated by the equivalence unit and counit.
Their two triangle identities cancel those inserted unit/counit pairs, leaving
the same fixed open restriction square on both paths.
Exact localization preserves the cube. Take the scalar mates, using the chosen
scalar adjunctions on both presentations. Their unit-preserving uniqueness map
is realizationScalarIso. Naturality and the triangle identities give the two
paths displayed here. No change of site, etale-origin witness, boundedness,
flatness, nonzero coefficient ring or nonempty scheme is involved. -/
theorem fixedOpenScalar_realization_transport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (K : _root_.DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Z)).homEquiv _ _).symm
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app
              ((sfIntrinsicDerivedEquivalence X A).functor.obj K)) ≫
          (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom.app
            ((pbcDerivedExtend (scalarRingMap φ X)).obj
              ((sfIntrinsicDerivedEquivalence X A).functor.obj K))) ≫
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory.map
        ((realizationScalarIso φ X).hom.app K) =
    (pbcDerivedExtend (scalarRingMap φ Z)).map ((openRealizationIso A j).hom.app K) ≫
      (realizationScalarIso φ Z).hom.app ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj K) ≫
      (sfIntrinsicDerivedEquivalence Z B).functor.map
        ((((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology Z) φ.ulift))).homEquiv _ _).symm
          ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.map
            (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology X) φ.ulift))).unit.app K) ≫
            (Functor.mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom.app
              ((ProEtale.pbcFixedScalarExtension (ProEt.topology X) φ.ulift).obj K))) ≫
      (openRealizationIso B j).inv.app
        ((ProEtale.pbcFixedScalarExtension (ProEt.topology X) φ.ulift).obj K) := by
  have h := scalar_mate_cube
    (sfIntrinsicDerivedEquivalence X A) (sfIntrinsicDerivedEquivalence X B)
    (sfIntrinsicDerivedEquivalence Z A) (sfIntrinsicDerivedEquivalence Z B)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology X) φ.ulift))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (ProEt.topology Z) φ.ulift))
    (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Z))
    (realizationScalarIso φ X) (realizationScalarIso φ Z)
    (mapDerivedCategorySquareIso (sfRealizationRestriction X φ))
    (mapDerivedCategorySquareIso (sfRealizationRestriction Z φ))
    (realization_scalar_unit X φ) (realization_scalar_unit Z φ)
    (openRealizationIso A j) (openRealizationIso B j)
    (mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom
    (mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom
    (realization_restriction_cube φ j) K
  simpa only [inverse_mate_app, ProEtale.pbcFixedScalarExtension,
    Functor.comp_obj, Functor.id_obj] using h

end AlgebraicGeometry.Scheme.FiniteCompactScalar
