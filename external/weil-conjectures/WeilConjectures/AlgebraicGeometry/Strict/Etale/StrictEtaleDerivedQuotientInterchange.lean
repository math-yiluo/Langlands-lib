/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Normalized derived quotient interchange

Source: Zheng, Construction 4.1 and Construction 5.15; Stacks Tags 03D7 and 06YT.
(blueprint: lem-pur-strict-etale-derived-quotient-interchange).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
private theorem derive_comparison
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    (QA : A ⥤ DA) (QB : B ⥤ DB) (W : MorphismProperty B) [QB.IsLocalization W]
    {F H : A ⥤ B} {R U : B ⥤ A} {FD HD : DA ⥤ DB} {RD UD : DB ⥤ DA}
    (a : F ⊣ R) (c : H ⊣ U) (ad : FD ⊣ RD) (cd : HD ⊣ UD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εH : QA ⋙ HD ⟶ H ⋙ QB)
    (ρF : R ⋙ QA ≅ QB ⋙ RD) (ρH : U ⋙ QA ≅ QB ⋙ UD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.hom.app K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH.app P ≫ QB.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH.hom.app K)
    (ν : F ≅ H) :
    ∃ i : FD ≅ HD, ∀ P, i.hom.app (QA.obj P) ≫ εH.app P =
      εF.app P ≫ QB.map (ν.hom.app P) := by
  let η := (conjugateIsoEquiv c a ν).symm
  let Ψ := Localization.fullyFaithfulWhiskeringLeft QB W DA
  let δ := Ψ.preimageIso
    (ρF.symm ≪≫ Functor.isoWhiskerRight η QA ≪≫ ρH)
  have hδ (K : B) : ρF.hom.app K ≫ δ.hom.app (QB.obj K) =
      QA.map (η.hom.app K) ≫ ρH.hom.app K := by
    have h := congr_app (Ψ.map_preimage
      (ρF.symm ≪≫ Functor.isoWhiskerRight η QA ≪≫ ρH).hom) K
    change δ.hom.app (QB.obj K) = _ at h
    rw [h]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, ← Category.assoc,
      Iso.hom_inv_id_app, Category.id_comp]
  have hν (P : A) : a.homEquiv _ _ (ν.hom.app P) ≫
      η.hom.app (H.obj P) = c.unit.app P := by
    apply (cancel_mono ((conjugateIsoEquiv c a ν).hom.app (H.obj P))).1
    simp only [Category.assoc, η, Iso.symm_hom, Iso.inv_hom_id_app,
      Category.comp_id]
    exact (unit_conjugateEquiv c a ν.hom P).symm
  refine ⟨(ad.ofNatIsoRight δ).leftAdjointUniq cd, ?_⟩
  exact normalizedAdjunction_uniqueness a c ad cd εF.app εH.app
    ρF.hom.app ρH.hom.app hF hH η δ ν.hom.app hν hδ

private theorem scalar_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ D} {S : D ⥤ B}
    {H : A ⥤ C} {V : C ⥤ A} {I : C ⥤ D} {W : D ⥤ C}
    [F.Additive] [R.Additive] [G.Additive] [S.Additive]
    [H.Additive] [V.Additive] [I.Additive] [W.Additive]
    {af : F ⊣ R} {ag : G ⊣ S} {ah : H ⊣ V} {ai : I ⊣ W}
    {pf : CochainComplex A ℤ → Prop} {pg : CochainComplex B ℤ → Prop}
    {ph : CochainComplex A ℤ → Prop} {pi : CochainComplex C ℤ → Prop}
    (df : DerivedCoefficientScalarExtension F R af pf)
    (dg : DerivedCoefficientScalarExtension G S ag pg)
    (dh : DerivedCoefficientScalarExtension H V ah ph)
    (di : DerivedCoefficientScalarExtension I W ai pi)
    (ν : F ⋙ G ≅ H ⋙ I) :
    ∃ d : df.derived ⋙ dg.derived ≅ dh.derived ⋙ di.derived, ∀ P,
      d.hom.app (DerivedCategory.Q.obj P) ≫
        di.derived.map (dh.counit.app P) ≫
        di.counit.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      dg.derived.map (df.counit.app P) ≫
        dg.counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Hc := H.mapHomologicalComplex (.up ℤ)
  let Ic := I.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let Sc := S.mapHomologicalComplex (.up ℤ)
  let Vc := V.mapHomologicalComplex (.up ℤ)
  let Wc := W.mapHomologicalComplex (.up ℤ)
  let εf : DerivedCategory.Q ⋙ (df.derived ⋙ dg.derived) ⟶
      (Fc ⋙ Gc) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight df.counit dg.derived ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Fc dg.counit ≫
      (Functor.associator _ _ _).inv
  let εh : DerivedCategory.Q ⋙ (dh.derived ⋙ di.derived) ⟶
      (Hc ⋙ Ic) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight dh.counit di.derived ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Hc di.counit ≫
      (Functor.associator _ _ _).inv
  let ρf : (Sc ⋙ Rc) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (dg.restriction ⋙ df.restriction) :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft Sc df.restrictionFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight dg.restrictionFactors.symm df.restriction ≪≫
      Functor.associator _ _ _
  let ρh : (Wc ⋙ Vc) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ (di.restriction ⋙ dh.restriction) :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft Wc dh.restrictionFactors.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight di.restrictionFactors.symm dh.restriction ≪≫
      Functor.associator _ _ _
  let νc : Fc ⋙ Gc ≅ Hc ⋙ Ic :=
    NatIso.mapHomologicalComplex ν (.up ℤ)
  have hf := normalizedAdjunction_composition
    (af.mapHomologicalComplex (.up ℤ)) (ag.mapHomologicalComplex (.up ℤ))
    df.derivedAdj dg.derivedAdj df.counit dg.counit
    df.restrictionFactors.inv dg.restrictionFactors.inv df.transpose dg.transpose
  have hh := normalizedAdjunction_composition
    (ah.mapHomologicalComplex (.up ℤ)) (ai.mapHomologicalComplex (.up ℤ))
    dh.derivedAdj di.derivedAdj dh.counit di.counit
    dh.restrictionFactors.inv di.restrictionFactors.inv dh.transpose di.transpose
  obtain ⟨d, hd⟩ := derive_comparison DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso D (.up ℤ))
    ((af.mapHomologicalComplex (.up ℤ)).comp (ag.mapHomologicalComplex (.up ℤ)))
    ((ah.mapHomologicalComplex (.up ℤ)).comp (ai.mapHomologicalComplex (.up ℤ)))
    (df.derivedAdj.comp dg.derivedAdj) (dh.derivedAdj.comp di.derivedAdj)
    εf εh ρf ρh
    (by
      intro P K f
      simpa only [εf, ρf, Fc, Gc, Rc, Sc, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using hf P K f)
    (by
      intro P K f
      simpa only [εh, ρh, Hc, Ic, Vc, Wc, Iso.trans_hom, Iso.symm_hom,
        NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using hh P K f)
    νc
  refine ⟨d, ?_⟩
  intro P
  simpa only [εf, εh, νc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hd P

namespace AlgebraicGeometry
private def restrictionSquare {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A B D E : Sheaf J RingCat.{u + 1}}
    (f : A ⟶ B) (g : D ⟶ E) (p : D ⟶ A) (q : E ⟶ B) (h : p ≫ f = g ≫ q) :
    restrictScalars.{u + 1} f ⋙ restrictScalars p ≅
      restrictScalars q ⋙ restrictScalars g :=
  pushforwardComp (F := 𝟭 C) (G := 𝟭 C) p f ≪≫ pushforwardCongr h ≪≫
    (pushforwardComp (F := 𝟭 C) (G := 𝟭 C) g q).symm

private theorem stageSquare
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index) {T : Scheme.{u}}
    {m n : ℕ} (h : n ≤ m) :
    coefficientQuotientMap (J := T.smallEtaleTopology) O ell (index.monotone h) ≫
        a.sheaf T n =
      a.sheaf T m ≫ coefficientQuotientMap (J := T.smallEtaleTopology) O' mu h := by
  change (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ =
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _ ≫
    (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change a.ring n (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)) (a.ring m (Ideal.Quotient.mk _ x))
  rw [a.generators, a.generators]
  rfl

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
  {phi : O →+* O'} {index : ℕ →o ℕ}
  {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}}

private def ordinaryRightIso {m n : ℕ} (h : n ≤ m) :
    restrictScalars.{u + 1} ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n)) ⋙
        coefficientRestriction (J := T.smallEtaleTopology) O ell (index.monotone h) ≅
      coefficientRestriction (J := T.smallEtaleTopology) O' mu h ⋙
        restrictScalars.{u + 1} ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T m)) := by
  apply restrictionSquare
  simpa only [Functor.map_comp] using congrArg
    (sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (stageSquare a h)

private def ordinaryComparison {m n : ℕ} (h : n ≤ m) :
    coefficientTensor (J := T.smallEtaleTopology) (O := O) (ell := ell)
      (index.monotone h) ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n) ≅
    siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T m) ⋙
      coefficientTensor (J := T.smallEtaleTopology) (O := O') (ell := mu) h :=
  (((coefficientTensorAdj (J := T.smallEtaleTopology) (O := O) (ell := ell)
    (index.monotone h)).comp
      (siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T n))).ofNatIsoRight
        (ordinaryRightIso h)).leftAdjointUniq
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf T m)).comp
      (coefficientTensorAdj (J := T.smallEtaleTopology) (O := O') (ell := mu) h))

end

end AlgebraicGeometry
