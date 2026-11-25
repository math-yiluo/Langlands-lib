/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismTransport
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-!
# Scalar association and automorphism transport

The canonical coefficient comparison commutes with successive scalar extensions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits
private theorem conjugate_associator_inv
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : B ⥤ C} {R₁ : C ⥤ B}
    {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (c : L₂ ⊣ R₂) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
        (Functor.associator L₀ L₁ L₂).inv =
      (Functor.associator R₂ R₁ R₀).inv := by
  apply (cancel_epi (Functor.associator R₂ R₁ R₀).hom).1
  rw [← conjugateEquiv_associator_hom a b c, conjugateEquiv_comp,
    Iso.inv_hom_id, conjugateEquiv_id, conjugateEquiv_associator_hom, Iso.hom_inv_id]

private theorem mate_scalar_square
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    {P₀ : A ⥤ A} {D₀ : A ⥤ A} {P₁ : B ⥤ B} {D₁ : B ⥤ B}
    {P₂ : C ⥤ C} {D₂ : C ⥤ C}
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd)
    (p₀ : P₀ ⊣ D₀) (p₁ : P₁ ⊣ D₁) (p₂ : P₂ ⊣ D₂)
    (r : Rk ⋙ Rh ≅ Rd)
    (sₕ : Rh ⋙ D₀ ≅ D₁ ⋙ Rh) (sₖ : Rk ⋙ D₁ ≅ D₂ ⋙ Rk)
    (s : Rd ⋙ D₀ ≅ D₂ ⋙ Rd)
    (hs : s.hom ≫ Functor.whiskerLeft D₂ r.inv =
      Functor.whiskerRight r.inv D₀ ≫ (Functor.associator Rk Rh D₀).hom ≫
        Functor.whiskerLeft Rk sₕ.hom ≫ (Functor.associator Rk D₁ Rh).inv ≫
        Functor.whiskerRight sₖ.hom Rh ≫ (Functor.associator D₂ Rk Rh).hom) :
    Functor.whiskerRight (Adjunction.leftAdjointCompIso a b d r).hom P₂ ≫
        ((conjugateIsoEquiv (p₀.comp d) (d.comp p₂)).symm s).hom =
      (Functor.associator Lh Lk P₂).hom ≫
        Functor.whiskerLeft Lh
          ((conjugateIsoEquiv (p₁.comp b) (b.comp p₂)).symm sₖ).hom ≫
        (Functor.associator Lh P₁ Lk).inv ≫
        Functor.whiskerRight
          ((conjugateIsoEquiv (p₀.comp a) (a.comp p₁)).symm sₕ).hom Lk ≫
        (Functor.associator P₀ Lh Lk).hom ≫
        Functor.whiskerLeft P₀ (Adjunction.leftAdjointCompIso a b d r).hom := by
  apply (conjugateEquiv (p₀.comp d) ((a.comp b).comp p₂)).injective
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp (p₀.comp d) (d.comp p₂) ((a.comp b).comp p₂)]
  rw [← conjugateEquiv_comp (p₀.comp d) (p₀.comp (a.comp b))
    ((a.comp b).comp p₂)]
  rw [← conjugateEquiv_comp (p₀.comp (a.comp b)) ((p₀.comp a).comp b)
    ((a.comp b).comp p₂)]
  rw [← conjugateEquiv_comp ((p₀.comp a).comp b) ((a.comp p₁).comp b)
    ((a.comp b).comp p₂)]
  rw [← conjugateEquiv_comp ((a.comp p₁).comp b) (a.comp (p₁.comp b))
    ((a.comp b).comp p₂)]
  rw [← conjugateEquiv_comp (a.comp (p₁.comp b)) (a.comp (b.comp p₂))
    ((a.comp b).comp p₂)]
  simpa only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugate_associator_inv,
    Adjunction.leftAdjointCompIso, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, Iso.symm_hom, Category.assoc] using hs

private theorem mate_scalar_square_app
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    {P₀ : A ⥤ A} {D₀ : A ⥤ A} {P₁ : B ⥤ B} {D₁ : B ⥤ B}
    {P₂ : C ⥤ C} {D₂ : C ⥤ C}
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd)
    (p₀ : P₀ ⊣ D₀) (p₁ : P₁ ⊣ D₁) (p₂ : P₂ ⊣ D₂)
    (r : Rk ⋙ Rh ≅ Rd)
    (sₕ : Rh ⋙ D₀ ≅ D₁ ⋙ Rh) (sₖ : Rk ⋙ D₁ ≅ D₂ ⋙ Rk)
    (s : Rd ⋙ D₀ ≅ D₂ ⋙ Rd)
    (hs : s.hom ≫ Functor.whiskerLeft D₂ r.inv =
      Functor.whiskerRight r.inv D₀ ≫ (Functor.associator Rk Rh D₀).hom ≫
        Functor.whiskerLeft Rk sₕ.hom ≫ (Functor.associator Rk D₁ Rh).inv ≫
        Functor.whiskerRight sₖ.hom Rh ≫ (Functor.associator D₂ Rk Rh).hom) (K : A) :
    P₂.map ((Adjunction.leftAdjointCompIso a b d r).hom.app K) ≫
        ((conjugateIsoEquiv (p₀.comp d) (d.comp p₂)).symm s).hom.app K =
      ((conjugateIsoEquiv (p₁.comp b) (b.comp p₂)).symm sₖ).hom.app (Lh.obj K) ≫
        Lk.map (((conjugateIsoEquiv (p₀.comp a) (a.comp p₁)).symm sₕ).hom.app K) ≫
        (Adjunction.leftAdjointCompIso a b d r).hom.app (P₀.obj K) := by
  have he := mate_scalar_square a b d p₀ p₁ p₂ r sₕ sₖ s hs
  have hx := NatTrans.congr_app he K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using hx

private theorem leftAdjointCompIso_eq
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd) (r : Rk ⋙ Rh ≅ Rd) :
    Adjunction.leftAdjointCompIso a b d r =
      ((a.comp b).ofNatIsoRight r).leftAdjointUniq d := by
  apply Iso.ext
  ext K
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointCompIso,
    conjugateEquiv_symm_apply_app]

private theorem normalized_associator
    {A B C AD BD CD : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* AD] [Category* BD] [Category* CD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (QC : C ⥤ CD)
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {H : A ⥤ C} {U : C ⥤ A}
    {FD : AD ⥤ BD} {RD : BD ⥤ AD} {GD : BD ⥤ CD} {SD : CD ⥤ BD}
    {HD : AD ⥤ CD} {UD : CD ⥤ AD}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U)
    (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC)
    (εH : QA ⋙ HD ⟶ H ⋙ QC)
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD)
    (ρH : U ⋙ QA ⟶ QC ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH.app P ≫ QC.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH.app K)
    (r : S ⋙ R ≅ U) (rd : SD ⋙ RD ≅ UD) (ν : F ⋙ G ≅ H)
    (hn : ∀ P, (a.comp b).homEquiv _ _ (ν.hom.app P) ≫
      r.hom.app (H.obj P) = c.unit.app P)
    (hr : ∀ K, (ρF.app (S.obj K) ≫ RD.map (ρG.app K)) ≫
      rd.hom.app (QC.obj K) = QA.map (r.hom.app K) ≫ ρH.app K)
    (P : A) :
    (Adjunction.leftAdjointCompIso ad bd cd rd).hom.app (QA.obj P) ≫ εH.app P =
      GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map (ν.hom.app P) := by
  have hc := normalizedAdjunction_composition a b ad bd εF εG ρF ρG hF hG
  have hu := normalizedAdjunction_uniqueness (QA := QA) (QB := QC) (a.comp b) c
    (ad.comp bd) cd
    (fun P ↦ GD.map (εF.app P) ≫ εG.app (F.obj P)) εH.app
    (fun K ↦ ρF.app (S.obj K) ≫ RD.map (ρG.app K)) ρH.app
    (by intro P K f; simpa only [Category.assoc] using hc P K f)
    hH r rd ν.hom.app hn hr P
  rw [← leftAdjointCompIso_eq] at hu
  simpa only [Category.assoc] using hu

private theorem complex_comparison_f
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (P : A ⥤ A) (S : B ⥤ B) [L.Additive] [P.Additive] [S.Additive]
    (c : L ⋙ S ≅ P ⋙ L) (K : CochainComplex A ℤ) (i : ℤ) :
    (((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ S)) (.up ℤ) ≪≫
      NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ L)) (.up ℤ)).symm).hom.app
        K).f i) = c.hom.app (K.X i) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Category.comp_id]

private def complexComparison
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    (L : A ⥤ B) (P : A ⥤ A) (S : B ⥤ B) [L.Additive] [P.Additive] [S.Additive]
    (c : L ⋙ S ≅ P ⋙ L) :
    L.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) ≅
      P.mapHomologicalComplex (.up ℤ) ⋙ L.mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ S)) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex c (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (P ⋙ L)) (.up ℤ)).symm

private theorem complex_square
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (Lh : A ⥤ B) (Lk : B ⥤ C) (Ld : A ⥤ C)
    (P₀ : A ⥤ A) (P₁ : B ⥤ B) (P₂ : C ⥤ C)
    [Lh.Additive] [Lk.Additive] [Ld.Additive]
    [P₀.Additive] [P₁.Additive] [P₂.Additive]
    (a : Lh ⋙ Lk ≅ Ld) (ch : Lh ⋙ P₁ ≅ P₀ ⋙ Lh)
    (ck : Lk ⋙ P₂ ≅ P₁ ⋙ Lk) (cd : Ld ⋙ P₂ ≅ P₀ ⋙ Ld)
    (hs : ∀ M, P₂.map (a.hom.app M) ≫ cd.hom.app M =
      ck.hom.app (Lh.obj M) ≫ Lk.map (ch.hom.app M) ≫ a.hom.app (P₀.obj M))
    (K : CochainComplex A ℤ) :
    (P₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
      (complexComparison Ld P₀ P₂ cd).hom.app K =
    (complexComparison Lk P₁ P₂ ck).hom.app ((Lh.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (Lk.mapHomologicalComplex (.up ℤ)).map
        ((complexComparison Lh P₀ P₁ ch).hom.app K) ≫
      (Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app
        ((P₀.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, complexComparison, complex_comparison_f]
  exact hs (K.X i)

private theorem complex_associator_unit
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {Lh : A ⥤ B} {Rh : B ⥤ A} {Lk : B ⥤ C} {Rk : C ⥤ B}
    {Ld : A ⥤ C} {Rd : C ⥤ A}
    [Lh.Additive] [Rh.Additive] [Lk.Additive] [Rk.Additive]
    [Ld.Additive] [Rd.Additive]
    (a : Lh ⊣ Rh) (b : Lk ⊣ Rk) (d : Ld ⊣ Rd) (r : Rk ⋙ Rh ≅ Rd)
    (P : CochainComplex A ℤ) :
    ((a.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ))).homEquiv
        _ _ ((Functor.mapHomologicalComplexCompIso
          (Adjunction.leftAdjointCompIso a b d r) (.up ℤ)).hom.app P) ≫
      (Functor.mapHomologicalComplexCompIso r (.up ℤ)).hom.app
        ((Ld.mapHomologicalComplex (.up ℤ)).obj P) =
      (d.mapHomologicalComplex (.up ℤ)).unit.app P := by
  rw [Adjunction.comp_homEquiv]
  change (a.mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((b.mapHomologicalComplex (.up ℤ)).homEquiv _ _ _) ≫ _ = _
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply HomologicalComplex.hom_ext
  intro i
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((a.comp b).ofNatIsoRight r) d (P.X i)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
    ← leftAdjointCompIso_eq a b d r] at hh
  change a.homEquiv _ _ (b.homEquiv _ _
    ((Adjunction.leftAdjointCompIso a b d r).hom.app (P.X i))) ≫
      r.hom.app (Ld.obj (P.X i)) = d.unit.app (P.X i) at hh
  change (a.unit.app (P.X i) ≫ Rh.map
    (b.unit.app (Lh.obj (P.X i)) ≫
      Rk.map ((Adjunction.leftAdjointCompIso a b d r).hom.app (P.X i)))) ≫
        r.hom.app (Ld.obj (P.X i)) = d.unit.app (P.X i)
  simpa only [Adjunction.homEquiv_unit] using hh

-- Normalizations determine the comparison square after successive extensions.
private theorem normalized_comparison_coherence
    {A B C AD BD CD : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* AD] [Category* BD] [Category* CD]
    (QA : A ⥤ AD) (QB : B ⥤ BD) (QC : C ⥤ CD)
    {Eh : A ⥤ B} {Ek : B ⥤ C} {Ed : A ⥤ C}
    {Lh : AD ⥤ BD} {Lk : BD ⥤ CD} {Ld : AD ⥤ CD}
    {U₀ : A ⥤ A} {U₁ : B ⥤ B} {U₂ : C ⥤ C}
    {P₀ : AD ⥤ AD} {P₁ : BD ⥤ BD} {P₂ : CD ⥤ CD}
    (θ₀ : QA ⋙ P₀ ≅ U₀ ⋙ QA) (θ₁ : QB ⋙ P₁ ≅ U₁ ⋙ QB)
    (θ₂ : QC ⋙ P₂ ≅ U₂ ⋙ QC)
    (εh : QA ⋙ Lh ⟶ Eh ⋙ QB) (εk : QB ⋙ Lk ⟶ Ek ⋙ QC)
    (εd : QA ⋙ Ld ⟶ Ed ⋙ QC)
    (a : Lh ⋙ Lk ≅ Ld) (ν : Eh ⋙ Ek ≅ Ed)
    (τh : Eh ⋙ U₁ ≅ U₀ ⋙ Eh) (τk : Ek ⋙ U₂ ≅ U₁ ⋙ Ek)
    (τd : Ed ⋙ U₂ ≅ U₀ ⋙ Ed)
    (ch : Lh ⋙ P₁ ≅ P₀ ⋙ Lh) (ck : Lk ⋙ P₂ ≅ P₁ ⋙ Lk)
    (cd : Ld ⋙ P₂ ≅ P₀ ⋙ Ld)
    (ha : ∀ X, a.hom.app (QA.obj X) ≫ εd.app X =
      Lk.map (εh.app X) ≫ εk.app (Eh.obj X) ≫ QC.map (ν.hom.app X))
    (hh : ∀ X, ch.hom.app (QA.obj X) ≫ Lh.map (θ₀.hom.app X) ≫ εh.app (U₀.obj X) =
      P₁.map (εh.app X) ≫ θ₁.hom.app (Eh.obj X) ≫ QB.map (τh.hom.app X))
    (hk : ∀ X, ck.hom.app (QB.obj X) ≫ Lk.map (θ₁.hom.app X) ≫ εk.app (U₁.obj X) =
      P₂.map (εk.app X) ≫ θ₂.hom.app (Ek.obj X) ≫ QC.map (τk.hom.app X))
    (ht : ∀ X, U₂.map (ν.hom.app X) ≫ τd.hom.app X =
      τk.hom.app (Eh.obj X) ≫ Ek.map (τh.hom.app X) ≫ ν.hom.app (U₀.obj X))
    (hu : ∀ c' : Ld ⋙ P₂ ≅ P₀ ⋙ Ld,
      (∀ X, c'.hom.app (QA.obj X) ≫ Ld.map (θ₀.hom.app X) ≫ εd.app (U₀.obj X) =
        P₂.map (εd.app X) ≫ θ₂.hom.app (Ed.obj X) ≫ QC.map (τd.hom.app X)) → c' = cd)
    (K : AD) :
    P₂.map (a.hom.app K) ≫ cd.hom.app K =
      ck.hom.app (Lh.obj K) ≫ Lk.map (ch.hom.app K) ≫ a.hom.app (P₀.obj K) := by
  let c' : Ld ⋙ P₂ ≅ P₀ ⋙ Ld :=
    Functor.isoWhiskerRight a.symm P₂ ≪≫ Functor.associator Lh Lk P₂ ≪≫
      Functor.isoWhiskerLeft Lh ck ≪≫ (Functor.associator Lh P₁ Lk).symm ≪≫
      Functor.isoWhiskerRight ch Lk ≪≫ Functor.associator P₀ Lh Lk ≪≫
      Functor.isoWhiskerLeft P₀ a
  have hc_app (X) : c'.hom.app X = P₂.map (a.inv.app X) ≫
      ck.hom.app (Lh.obj X) ≫ Lk.map (ch.hom.app X) ≫ a.hom.app (P₀.obj X) := by
    simp [c']
  have hc' : c' = cd := by
    apply hu
    intro X
    have han := a.hom.naturality (θ₀.hom.app X)
    have hcn := ck.hom.naturality (εh.app X)
    have hε := εk.naturality (τh.hom.app X)
    have hθ := θ₂.hom.naturality (ν.hom.app X)
    simp only [Functor.comp_map] at han hcn hε hθ
    apply (cancel_epi (P₂.map (a.hom.app (QA.obj X)))).1
    rw [hc_app]
    simp only [Category.assoc]
    rw [← P₂.map_comp_assoc, a.hom_inv_id_app, P₂.map_id, Category.id_comp]
    rw [← reassoc_of% han, ha]
    conv_lhs => rw [← Lk.map_comp_assoc, ← Lk.map_comp_assoc]
    simp only [Category.assoc]
    rw [hh]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hcn, reassoc_of% hε, reassoc_of% (hk (Eh.obj X))]
    conv_rhs => rw [← P₂.map_comp_assoc]
    rw [ha]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hθ]
    have he := congrArg (fun f ↦ QC.map f) (ht X)
    simp only [Functor.map_comp] at he
    exact congrArg (fun f ↦ P₂.map (Lk.map (εh.app X)) ≫
      P₂.map (εk.app (Eh.obj X)) ≫ θ₂.hom.app (Ek.obj (Eh.obj X)) ≫ f) he.symm
  rw [← hc', hc_app, ← P₂.map_comp_assoc, a.hom_inv_id_app, P₂.map_id, Category.id_comp]

namespace AlgebraicGeometry.Scheme

private theorem tensorComplexCounit_eq {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (P : CochainComplex (pbcModules X R) ℤ) :
    pbcComplexCounit φ P = (pbcExtensionCounit φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  simp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors]
  erw [(pbcDerivedExtend φ).map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id]

private def tensorComplexCounit {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    DerivedCategory.Q ⋙ pbcDerivedExtend φ ⟶
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app := pbcComplexCounit φ
  naturality := by
    intro P K f
    rw [tensorComplexCounit_eq, tensorComplexCounit_eq]
    exact (pbcExtensionCounit φ).naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map f)

attribute [local irreducible] complexComparison

private theorem restrict_comp_inverse_section {X : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (w : φ ≫ ψ = χ)
    (M : pbcModules X B) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ w).inv.app M).val.app U x = x := by
  have hx := (pbcRestrictComp_exists φ ψ χ w).exists.choose_spec M U x
  have hi := congrArg (fun f ↦ f.val.app U x) ((pbcRestrictComp φ ψ χ w).hom_inv_id_app M)
  exact (congrArg (fun y ↦ ((pbcRestrictComp φ ψ χ w).inv.app M).val.app U y) hx).symm.trans hi

private theorem sectionwise_right_square {X : Scheme.{u}} (f : X ⟶ X)
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (cR : (proEtaleSheafInverseImage f CommRingCat).obj R ≅ R)
    (cS : (proEtaleSheafInverseImage f CommRingCat).obj S ≅ S)
    (cB : (proEtaleSheafInverseImage f CommRingCat).obj B ≅ B)
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (w : φ ≫ ψ = χ)
    (sh : pbcRestrict φ ⋙ proEtaleRingModuleDirectImage f R R cR ≅
      proEtaleRingModuleDirectImage f S S cS ⋙ pbcRestrict φ)
    (sk : pbcRestrict ψ ⋙ proEtaleRingModuleDirectImage f S S cS ≅
      proEtaleRingModuleDirectImage f B B cB ⋙ pbcRestrict ψ)
    (sd : pbcRestrict χ ⋙ proEtaleRingModuleDirectImage f R R cR ≅
      proEtaleRingModuleDirectImage f B B cB ⋙ pbcRestrict χ)
    (hh : ∀ (M : pbcModules X S) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleBaseChange f).op.obj U)),
      (sh.hom.app M).val.app U x = x)
    (hk : ∀ (M : pbcModules X B) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleBaseChange f).op.obj U)),
      (sk.hom.app M).val.app U x = x)
    (hd : ∀ (M : pbcModules X B) (U : X.ProEtᵒᵖ)
      (x : M.val.obj ((proEtaleBaseChange f).op.obj U)),
      (sd.hom.app M).val.app U x = x) :
    sd.hom ≫ Functor.whiskerLeft (proEtaleRingModuleDirectImage f B B cB)
        (pbcRestrictComp φ ψ χ w).inv =
      Functor.whiskerRight (pbcRestrictComp φ ψ χ w).inv
          (proEtaleRingModuleDirectImage f R R cR) ≫
        (Functor.associator (pbcRestrict ψ) (pbcRestrict φ)
          (proEtaleRingModuleDirectImage f R R cR)).hom ≫
        Functor.whiskerLeft (pbcRestrict ψ) sh.hom ≫
        (Functor.associator (pbcRestrict ψ) (proEtaleRingModuleDirectImage f S S cS)
          (pbcRestrict φ)).inv ≫
        Functor.whiskerRight sk.hom (pbcRestrict φ) ≫
        (Functor.associator (proEtaleRingModuleDirectImage f B B cB)
          (pbcRestrict ψ) (pbcRestrict φ)).hom := by
  ext M U x
  change ((pbcRestrictComp φ ψ χ w).inv.app
      ((proEtaleRingModuleDirectImage f B B cB).obj M)).val.app U
        ((sd.hom.app M).val.app U x) =
    (sk.hom.app M).val.app U
      ((sh.hom.app ((pbcRestrict ψ).obj M)).val.app U
        (((pbcRestrictComp φ ψ χ w).inv.app M).val.app
          ((proEtaleBaseChange f).op.obj U) x))
  erw [hd, restrict_comp_inverse_section, restrict_comp_inverse_section, hh, hk]

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {T : Scheme.{u}} (e : Aut T) [IsNoetherian T]
  {E F G : Padic.FiniteCoefficientFields l Ω}

attribute [local irreducible] pbcExtensionCounit pbcComplexCounit pbcScalarAdjunction
  pbcDerivedScalarAdjunction pbcIsoOrdinaryScalarComparison pbcIsoOrdinaryComplexComparison
  pbcIsoAmbientScalarComparison pbcAmbientScalarAssociator
  proEtaleRingModulePullback completedModulePullback Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors completedPullbackComparison completedPullbackObject
  completedCoefficientMap pbcCompletedScalarMap reductionChange reductionDerivedChange

private def ordinaryAssociator (h : E ≤ F) (k : F ≤ G) :
    pbcExtend (pbcCompletedScalarMap l Ω T h) ⋙
        pbcExtend (pbcCompletedScalarMap l Ω T k) ≅
      pbcExtend (pbcCompletedScalarMap l Ω T (h.trans k)) :=
  Adjunction.leftAdjointCompIso
    (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T h))
    (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T k))
    (pbcScalarAdjunction (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcRestrictComp (pbcCompletedScalarMap l Ω T h)
      (pbcCompletedScalarMap l Ω T k) (pbcCompletedScalarMap l Ω T (h.trans k))
      (pbcCompletedScalarMap_comp l Ω T h k))

private def complexAssociator (h : E ≤ F) (k : F ≤ G) :
    (pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ) ⋙
        (pbcExtend (pbcCompletedScalarMap l Ω T k)).mapHomologicalComplex (.up ℤ) ≅
      (pbcExtend (pbcCompletedScalarMap l Ω T (h.trans k))).mapHomologicalComplex
        (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (ordinaryAssociator l Ω h k) (.up ℤ)

omit [IsNoetherian T] in
private theorem right_comparison_section (h : E ≤ F)
    (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F)))
    (U : T.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleBaseChange e.asIso.hom).op.obj U)) :
    ((pbcIsoScalarRightComparison l Ω e h).hom.app M).val.app U x = x := by
  exact eq_of_heq ((pbcIsoScalarRightComparison_exists l Ω e h).exists.choose_spec M U x)

private theorem ordinary_coherence (h : E ≤ F) (k : F ≤ G)
    (M : pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) :
    (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).map
        ((ordinaryAssociator l Ω h k).hom.app M) ≫
      (pbcIsoOrdinaryScalarComparison l Ω e (h.trans k)).hom.app M =
    (pbcIsoOrdinaryScalarComparison l Ω e k).hom.app
        ((pbcExtend (pbcCompletedScalarMap l Ω T h)).obj M) ≫
      (pbcExtend (pbcCompletedScalarMap l Ω T k)).map
        ((pbcIsoOrdinaryScalarComparison l Ω e h).hom.app M) ≫
      (ordinaryAssociator l Ω h k).hom.app
        ((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj M) := by
  let φ := pbcCompletedScalarMap l Ω T h
  let ψ := pbcCompletedScalarMap l Ω T k
  let χ := pbcCompletedScalarMap l Ω T (h.trans k)
  let D₀ := proEtaleRingModuleDirectImage e.asIso.hom
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))
    (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E)))
  let D₁ := proEtaleRingModuleDirectImage e.asIso.hom
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω F))
    (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω F)))
  let D₂ := proEtaleRingModuleDirectImage e.asIso.hom
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω G))
    (pbcAdicCompletion T (pbcStageDatum.{u} l Ω G))
    (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω G)))
  let r := pbcRestrictComp φ ψ χ (pbcCompletedScalarMap_comp l Ω T h k)
  let sh := pbcIsoScalarRightComparison l Ω e h
  let sk := pbcIsoScalarRightComparison l Ω e k
  let sd := pbcIsoScalarRightComparison l Ω e (h.trans k)
  have hs : sd.hom ≫ Functor.whiskerLeft D₂ r.inv =
      Functor.whiskerRight r.inv D₀ ≫
        (Functor.associator (pbcRestrict ψ) (pbcRestrict φ) D₀).hom ≫
        Functor.whiskerLeft (pbcRestrict ψ) sh.hom ≫
        (Functor.associator (pbcRestrict ψ) D₁ (pbcRestrict φ)).inv ≫
        Functor.whiskerRight sk.hom (pbcRestrict φ) ≫
        (Functor.associator D₂ (pbcRestrict ψ) (pbcRestrict φ)).hom := by
    exact sectionwise_right_square e.asIso.hom _ _ _ φ ψ χ
      (pbcCompletedScalarMap_comp l Ω T h k) sh sk sd
      (right_comparison_section l Ω e h)
      (right_comparison_section l Ω e k)
      (right_comparison_section l Ω e (h.trans k))
  have hh := mate_scalar_square_app (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
    (pbcScalarAdjunction χ)
    (proEtaleRingModuleAdjunction e.asIso.hom _ _
      (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω E))))
    (proEtaleRingModuleAdjunction e.asIso.hom _ _
      (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω F))))
    (proEtaleRingModuleAdjunction e.asIso.hom _ _
      (asIso (completedCoefficientMap e.asIso.hom (pbcStageDatum.{u} l Ω G)))) r sh sk sd hs M
  unfold ordinaryAssociator pbcIsoOrdinaryScalarComparison
  exact hh

omit [IsNoetherian T] in
private theorem complexComparison_eq (h : E ≤ F) :
    pbcIsoOrdinaryComplexComparison l Ω e h =
      complexComparison (pbcExtend (pbcCompletedScalarMap l Ω T h))
        (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E))
        (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F))
        (pbcIsoOrdinaryScalarComparison l Ω e h) := by
  unfold pbcIsoOrdinaryComplexComparison complexComparison
  rfl

private theorem complex_coherence (h : E ≤ F) (k : F ≤ G)
    (P : CochainComplex
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    ((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).mapHomologicalComplex
        (.up ℤ)).map ((complexAssociator l Ω h k).hom.app P) ≫
      (pbcIsoOrdinaryComplexComparison l Ω e (h.trans k)).hom.app P =
    (pbcIsoOrdinaryComplexComparison l Ω e k).hom.app
        (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      ((pbcExtend (pbcCompletedScalarMap l Ω T k)).mapHomologicalComplex (.up ℤ)).map
        ((pbcIsoOrdinaryComplexComparison l Ω e h).hom.app P) ≫
      (complexAssociator l Ω h k).hom.app
        (((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
          (.up ℤ)).obj P) := by
  unfold complexAssociator
  rw [complexComparison_eq l Ω e (h.trans k), complexComparison_eq l Ω e k,
    complexComparison_eq l Ω e h]
  exact complex_square
      (pbcExtend (pbcCompletedScalarMap l Ω T h))
      (pbcExtend (pbcCompletedScalarMap l Ω T k))
      (pbcExtend (pbcCompletedScalarMap l Ω T (h.trans k)))
      (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E))
      (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F))
      (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω G))
      (ordinaryAssociator l Ω h k)
      (pbcIsoOrdinaryScalarComparison l Ω e h)
      (pbcIsoOrdinaryScalarComparison l Ω e k)
      (pbcIsoOrdinaryScalarComparison l Ω e (h.trans k))
      (ordinary_coherence l Ω e h k) P

private theorem extensionAssociator_normalization {X : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (w : φ ≫ ψ = χ)
    (P : CochainComplex (pbcModules X R) ℤ) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
        (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
        (pbcDerivedRestrictComp φ ψ χ w)).hom.app (DerivedCategory.Q.obj P) ≫
      pbcComplexCounit χ P =
    (pbcDerivedExtend ψ).map (pbcComplexCounit φ P) ≫
      pbcComplexCounit ψ (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Adjunction.leftAdjointCompIso (pbcScalarAdjunction φ) (pbcScalarAdjunction ψ)
            (pbcScalarAdjunction χ) (pbcRestrictComp φ ψ χ w)) (.up ℤ)).hom.app P) := by
  let a := pbcScalarAdjunction φ
  let b := pbcScalarAdjunction ψ
  let d := pbcScalarAdjunction χ
  let r := pbcRestrictComp φ ψ χ (w)
  let rd := pbcDerivedRestrictComp φ ψ χ (w)
  let ac := a.mapHomologicalComplex (.up ℤ)
  let bc := b.mapHomologicalComplex (.up ℤ)
  let dc := d.mapHomologicalComplex (.up ℤ)
  let rc := Functor.mapHomologicalComplexCompIso r (.up ℤ)
  let νc := Functor.mapHomologicalComplexCompIso
    (Adjunction.leftAdjointCompIso a b d r) (.up ℤ)
  have hn (P) : (ac.comp bc).homEquiv _ _ (νc.hom.app P) ≫
      rc.hom.app (((pbcExtend χ).mapHomologicalComplex (.up ℤ)).obj P) = dc.unit.app P := by
    exact complex_associator_unit a b d r P
  have hh := normalized_associator DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ac bc dc (pbcDerivedScalarAdjunction φ) (pbcDerivedScalarAdjunction ψ)
    (pbcDerivedScalarAdjunction χ)
    (tensorComplexCounit φ) (tensorComplexCounit ψ) (tensorComplexCounit χ)
    (pbcRestrict φ).mapDerivedCategoryFactors.inv
    (pbcRestrict ψ).mapDerivedCategoryFactors.inv
    (pbcRestrict χ).mapDerivedCategoryFactors.inv
    (pbcAdjunction_complexTranspose X φ) (pbcAdjunction_complexTranspose X ψ)
    (pbcAdjunction_complexTranspose X χ) rc rd νc hn
    (by
      intro K
      simpa only [rd, rc, pbcDerivedRestrictComp, pbcDerivedRestrict,
        Functor.exactDerivedRestrictionComposition, Functor.mapHomologicalComplexCompIso,
        Category.assoc] using
        Functor.exactDerivedRestrictionComposition_inv_factors
          (pbcRestrict ψ) (pbcRestrict φ) (pbcRestrict χ) r K) P
  exact hh

private theorem ambientAssociator_normalization (h : E ≤ F) (k : F ≤ G)
    (P : CochainComplex
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    (pbcAmbientScalarAssociator l Ω T h k).hom.app (DerivedCategory.Q.obj P) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T (h.trans k)) P =
      (pbcAmbientScalarExtension l Ω T k).map
          (pbcComplexCounit (pbcCompletedScalarMap l Ω T h) P) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T k)
          (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((complexAssociator l Ω h k).hom.app P) := by
  unfold pbcAmbientScalarAssociator complexAssociator ordinaryAssociator
  exact extensionAssociator_normalization
    (pbcCompletedScalarMap l Ω T h) (pbcCompletedScalarMap l Ω T k)
    (pbcCompletedScalarMap l Ω T (h.trans k)) (pbcCompletedScalarMap_comp l Ω T h k) P

omit [IsNoetherian T] in
private theorem ambient_comparison_normalization (h : E ≤ F)
    (P : CochainComplex
      (pbcModules T (pbcAdicCompletion T (pbcStageDatum.{u} l Ω E))) ℤ) :
    (pbcIsoAmbientScalarComparison l Ω e h).hom.app (DerivedCategory.Q.obj P) ≫
      (pbcAmbientScalarExtension l Ω T h).map
        ((pbcIsoModulePullback e.asIso.hom
          (pbcStageDatum.{u} l Ω E)).mapDerivedCategoryFactors.hom.app P) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).mapHomologicalComplex
          (.up ℤ)).obj P) =
    (pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω F)).map
        (pbcComplexCounit (pbcCompletedScalarMap l Ω T h) P) ≫
      (pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F)).mapDerivedCategoryFactors.hom.app
        (((pbcExtend (pbcCompletedScalarMap l Ω T h)).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((pbcIsoOrdinaryComplexComparison l Ω e h).hom.app P) :=
by
  unfold pbcIsoAmbientScalarComparison
  exact (pbcIsoAmbientScalarComparison_exists l Ω e h).exists.choose_spec P

private theorem ambient_coherence (h : E ≤ F) (k : F ≤ G)
    (K : pbcAmbientStage l Ω T E) :
    (pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).map
        ((pbcAmbientScalarAssociator l Ω T h k).hom.app K) ≫
      (pbcIsoAmbientScalarComparison l Ω e (h.trans k)).hom.app K =
    (pbcIsoAmbientScalarComparison l Ω e k).hom.app
        ((pbcAmbientScalarExtension l Ω T h).obj K) ≫
      (pbcAmbientScalarExtension l Ω T k).map
        ((pbcIsoAmbientScalarComparison l Ω e h).hom.app K) ≫
      (pbcAmbientScalarAssociator l Ω T h k).hom.app
        ((pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj K) := by
  -- The universal derived comparison is uniquely determined on complexes.
  have hh := normalized_comparison_coherence DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).mapDerivedCategoryFactors)
    ((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω F)).mapDerivedCategoryFactors)
    ((pbcIsoModulePullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).mapDerivedCategoryFactors)
    (tensorComplexCounit (pbcCompletedScalarMap l Ω T h))
    (tensorComplexCounit (pbcCompletedScalarMap l Ω T k))
    (tensorComplexCounit (pbcCompletedScalarMap l Ω T (h.trans k)))
    (pbcAmbientScalarAssociator l Ω T h k) (complexAssociator l Ω h k)
    (pbcIsoOrdinaryComplexComparison l Ω e h)
    (pbcIsoOrdinaryComplexComparison l Ω e k)
    (pbcIsoOrdinaryComplexComparison l Ω e (h.trans k))
    (pbcIsoAmbientScalarComparison l Ω e h)
    (pbcIsoAmbientScalarComparison l Ω e k)
    (pbcIsoAmbientScalarComparison l Ω e (h.trans k))
    (ambientAssociator_normalization l Ω h k)
    (ambient_comparison_normalization l Ω e h)
    (ambient_comparison_normalization l Ω e k)
    (complex_coherence l Ω e h k) (fun c' hc' ↦ ?_) K
  · exact hh
  · apply (pbcIsoAmbientScalarComparison_exists l Ω e (h.trans k)).unique
    · exact hc'
    · exact ambient_comparison_normalization l Ω e (h.trans k)

variable (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

private theorem integral_comparison_hom (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K).hom =
      (pbcIsoAmbientScalarComparison l Ω e h).hom.app K.obj := by
  exact congrArg (fun t ↦ t.app K)
    (pbcIsoIntegralScalarComparison_exists l Ω e hdim hl h).exists.choose_spec

private theorem integral_coherence (h : E ≤ F) (k : F ≤ G)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).map
        ((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
      (pbcIsoIntegralScalarComparison l Ω e hdim hl (h.trans k)).hom.app K =
    (pbcIsoIntegralScalarComparison l Ω e hdim hl k).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcIntegralScalarExtension l Ω T hdim hl k).map
        ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) ≫
      (pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app
        ((pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj K) := by
  apply ObjectProperty.hom_ext
  change (pbcIsoAmbientPullback e.asIso.hom (pbcStageDatum.{u} l Ω G)).map
        (((pbcIntegralScalarAssociator l Ω T hdim hl h k).hom.app K).hom) ≫ _ = _
  dsimp only [pbcIntegralScalarExtension, pbcIsoIntegralPullback, ObjectProperty.lift,
    Functor.comp_obj, Functor.comp_map, pbcStageInclusion, ObjectProperty.ι, inducedFunctor]
  simp only [ObjectProperty.FullSubcategory.comp_hom, pbcIntegralScalarAssociator_hom,
    integral_comparison_hom]
  exact ambient_coherence l Ω e h k K.obj

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {T : Scheme.{u}} (e : Aut T)
  [IsNoetherian T] (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
  (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
  {E F G : Padic.FiniteCoefficientFields l Ω}

private theorem rationalization_hom (H : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω T H) :
    (eqToIso (pbcIsoRationalization l Ω e H)).hom.app K = 𝟙 _ := by
  simp only [eqToIso.hom, eqToHom_app]
  rfl

private theorem rationalization_inv (H : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω T H) :
    (eqToIso (pbcIsoRationalization l Ω e H)).inv.app K = 𝟙 _ := by
  simp only [eqToIso.inv, eqToHom_app]
  rfl

private theorem rational_comparison_normalization (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIsoRationalScalarComparison l Ω e hdim hl h).hom.app
        ((pbcStageLocalization l Ω T E).obj K) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl h).hom.app
        ((pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj K) =
    (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F)
        (pbcStageUniformizer.{u} l Ω F)).map
        ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
      (pbcStageLocalization l Ω T F).map
        ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) := by
  dsimp only [pbcIsoRationalScalarComparison]
  rw [(pbcIsoRationalScalarComparison_exists l Ω e hdim hl h).exists.choose_spec K]
  rw [rationalization_hom, rationalization_inv]
  simp only [Category.assoc]
  erw [Category.id_comp, (pbcScalarExtension l Ω T hdim hl h).map_id,
    Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

private theorem rational_comparison_normalization_full (h : E ≤ F)
    (K : pbcIntegralStage l Ω T E) :
    (pbcIsoRationalScalarComparison l Ω e hdim hl h).hom.app
        ((pbcStageLocalization l Ω T E).obj K) ≫
      (pbcScalarExtension l Ω T hdim hl h).map
        ((eqToIso (pbcIsoRationalization l Ω e E)).hom.app K) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl h).hom.app
        ((pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj K) =
    (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω F)
        (pbcStageUniformizer.{u} l Ω F)).map
        ((pbcScalarIntegralComparison l Ω T hdim hl h).hom.app K) ≫
      (eqToIso (pbcIsoRationalization l Ω e F)).hom.app
        ((pbcIntegralScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcStageLocalization l Ω T F).map
        ((pbcIsoIntegralScalarComparison l Ω e hdim hl h).hom.app K) := by
  rw [rationalization_hom, rationalization_hom]
  erw [(pbcScalarExtension l Ω T hdim hl h).map_id,
    Category.id_comp, Category.id_comp]
  exact rational_comparison_normalization l Ω e hdim hl h K

attribute [local irreducible] pbcIsoRationalScalarComparison pbcScalarIntegralComparison
  pbcScalarAssociator pbcIntegralScalarAssociator pbcIsoIntegralScalarComparison
  pbcScalarExtension pbcIntegralScalarExtension pbcIsoIntegralPullback

/-- The scalar associator commutes with the canonical automorphism comparison. -/
theorem pbcIsoRationalScalarComparison_comp (h : E ≤ F) (k : F ≤ G)
    (K : pbcStageCategory l Ω T E) :
    (pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω G)
        (pbcStageUniformizer.{u} l Ω G)).map
        ((pbcScalarAssociator l Ω T hdim hl h k).hom.app K) ≫
      (pbcIsoRationalScalarComparison l Ω e hdim hl (h.trans k)).hom.app K =
    (pbcIsoRationalScalarComparison l Ω e hdim hl k).hom.app
        ((pbcScalarExtension l Ω T hdim hl h).obj K) ≫
      (pbcScalarExtension l Ω T hdim hl k).map
        ((pbcIsoRationalScalarComparison l Ω e hdim hl h).hom.app K) ≫
      (pbcScalarAssociator l Ω T hdim hl h k).hom.app
        ((pbcRationalIsoPullback e (pbcStageDatum.{u} l Ω E)
          (pbcStageUniformizer.{u} l Ω E)).obj K) := by
  -- The same calculation descends through rational localization.
  apply normalized_comparison_coherence
    (pbcStageLocalization l Ω T E) (pbcStageLocalization l Ω T F)
    (pbcStageLocalization l Ω T G)
    (eqToIso (pbcIsoRationalization l Ω e E))
    (eqToIso (pbcIsoRationalization l Ω e F))
    (eqToIso (pbcIsoRationalization l Ω e G))
    (pbcScalarIntegralComparison l Ω T hdim hl h).hom
    (pbcScalarIntegralComparison l Ω T hdim hl k).hom
    (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).hom
    (pbcScalarAssociator l Ω T hdim hl h k)
    (pbcIntegralScalarAssociator l Ω T hdim hl h k)
    (pbcIsoIntegralScalarComparison l Ω e hdim hl h)
    (pbcIsoIntegralScalarComparison l Ω e hdim hl k)
    (pbcIsoIntegralScalarComparison l Ω e hdim hl (h.trans k))
    (pbcIsoRationalScalarComparison l Ω e hdim hl h)
    (pbcIsoRationalScalarComparison l Ω e hdim hl k)
    (pbcIsoRationalScalarComparison l Ω e hdim hl (h.trans k))
    (pbcScalarAssociator_normalization l Ω T hdim hl h k)
    (rational_comparison_normalization_full l Ω e hdim hl h)
    (rational_comparison_normalization_full l Ω e hdim hl k)
    (integral_coherence l Ω e hdim hl h k) ?_ K
  intro c' hc'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  obtain ⟨X⟩ := X
  apply (cancel_mono
    ((pbcScalarExtension l Ω T hdim hl (h.trans k)).map
        ((eqToIso (pbcIsoRationalization l Ω e E)).hom.app X) ≫
      (pbcScalarIntegralComparison l Ω T hdim hl (h.trans k)).hom.app
        ((pbcIsoIntegralPullback e.asIso.hom (pbcStageDatum.{u} l Ω E)).obj X))).1
  exact (hc' X).trans
    (rational_comparison_normalization_full l Ω e hdim hl (h.trans k) X).symm

end AlgebraicGeometry.Scheme
