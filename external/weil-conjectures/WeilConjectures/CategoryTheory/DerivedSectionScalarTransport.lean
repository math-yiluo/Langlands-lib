/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.ScalarInternalHomData
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Transport of normalized derived scalar adjunctions

Source: Stacks Project, Derived Categories, Tag 09T5; Cohomology on Sites,
Tags 06YY and 07A6. This isolates localization and the derived unit normalization
from the concrete balanced-generator calculation.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits

-- Upstream made these instances local in InternalSectionTensorComparison.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

private theorem kan_postcomp_iff
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (Q : A ⥤ B) (F : A ⥤ D) (T : B ⥤ D) (α : Q ⋙ T ⟶ F)
    (H : D ⥤ E) [H.IsEquivalence] :
    T.IsRightKanExtension α ↔ (T ⋙ H).IsRightKanExtension
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α H) := by
  have : (Functor.RightExtension.postcompose₂ Q F H).IsEquivalence := by
    have : IsIso
        ({ app := fun X ↦ (Functor.associator Q X H).inv } :
          (Functor.whiskeringRight B D E).obj H ⋙
            (Functor.whiskeringLeft A B E).obj Q ⟶
          (Functor.whiskeringLeft A B D).obj Q ⋙
            (Functor.whiskeringRight A D E).obj H) :=
      NatIso.isIso_of_isIso_app _
    apply CostructuredArrow.isEquivalenceMap₂
  let e := (IsTerminal.isTerminalIffObj (Functor.RightExtension.postcompose₂ Q F H)
    (Functor.RightExtension.mk T α)).trans
      (IsTerminal.equivOfIso (Functor.RightExtension.postcompose₂ObjMkIso H α))
  constructor
  · intro h
    exact ⟨⟨e (T.isUniversalOfIsRightKanExtension α)⟩⟩
  · intro h
    exact ⟨⟨e.symm ((T ⋙ H).isUniversalOfIsRightKanExtension _)⟩⟩

private theorem kan_transport
    {A A' B B' D E : Type*}
    [Category A] [Category A'] [Category B] [Category B'] [Category D] [Category E]
    (G : A ⥤ A') [G.IsEquivalence] (H : D ⥤ E) [H.IsEquivalence]
    (K : B ⥤ B') [K.IsEquivalence]
    (Q : A ⥤ B) (Q' : A' ⥤ B') (F : A ⥤ D) (F' : A' ⥤ E)
    (T : B ⥤ D) (T' : B' ⥤ E)
    (eQ : Q ⋙ K ≅ G ⋙ Q') (eF : F ⋙ H ≅ G ⋙ F') (eT : T ⋙ H ≅ K ⋙ T')
    (α : Q ⋙ T ⟶ F) (α' : Q' ⋙ T' ⟶ F')
    (hα : ∀ X, H.map (α.app X) ≫ eF.hom.app X =
      eT.hom.app (Q.obj X) ≫ T'.map (eQ.hom.app X) ≫ α'.app (G.obj X))
    [T'.IsRightKanExtension α'] : T.IsRightKanExtension α := by
  apply (kan_postcomp_iff Q F T α H).mpr
  let β := (Functor.associator G Q' T').hom ≫ Functor.whiskerLeft G α'
  have hβ : T'.IsRightKanExtension β :=
    (Functor.isRightKanExtension_iff_precomp T' G α').mp inferInstance
  let γ := (Functor.associator Q K T').inv ≫ Functor.whiskerRight eQ.hom T' ≫ β
  have hγ : (K ⋙ T').IsRightKanExtension γ :=
    (Functor.isRightKanExtension_iff_postcomp₁ K eQ β).mp hβ
  apply (Functor.isRightKanExtension_iff_of_iso₂
    ((Functor.associator Q T H).inv ≫ Functor.whiskerRight α H) γ eF eT ?_).mpr hγ
  ext X
  simpa [γ, β] using (hα X).symm

private theorem derived_square_fac
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (U : A ⥤ B) (G : B ⥤ E) (H : A ⥤ D) (V : D ⥤ E)
    [U.Additive] [G.Additive] [H.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (e : U ⋙ G ≅ H ⋙ V) (P : CochainComplex A ℤ) :
    let ed := Functor.mapDerivedCategoryCompIso U G ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso H V).symm
    let ec := (Functor.mapHomologicalComplexCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).symm ≪≫
      NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
      Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ V)) (.up ℤ)
    ed.hom.app (DerivedCategory.Q.obj P) ≫
        V.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
        V.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (ec.hom.app P) := by
  dsimp only
  have hu := Functor.mapDerivedCategoryCompIso_fac U G P
  have hh := Functor.mapDerivedCategoryCompIso_fac H V P
  have he := Functor.mapDerivedCategoryNatIso_fac e P
  change (Functor.mapDerivedCategoryCompIso U G).inv.app (DerivedCategory.Q.obj P) ≫
    G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (𝟙 _) = _ at hu
  change (Functor.mapDerivedCategoryCompIso H V).inv.app (DerivedCategory.Q.obj P) ≫
    V.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
    V.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (𝟙 _) = _ at hh
  erw [Functor.map_id, Category.comp_id] at hu hh
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hh, he]
  rw [← Category.assoc, ← hu]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  change _ = G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (𝟙 _) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
      DerivedCategory.Q.map (𝟙 _)
  erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.id_comp]

-- Keep the conjugation data abstract while checking its normalization equations.
private noncomputable def transportedLeft
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ D) (G : D ⥤ E) (e : B ≌ E) : A ⥤ B :=
  (F ⋙ G) ⋙ e.inverse

private noncomputable def transportedLeftIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (F : A ⥤ D) (G : D ⥤ E) (e : B ≌ E) :
    transportedLeft F G e ⋙ e.functor ≅ F ⋙ G :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.counitIso ≪≫
    Functor.rightUnitor _

attribute [local irreducible] transportedLeft transportedLeftIso

private noncomputable def transportedAdjunction
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : A ⥤ D} {G : B ⥤ E}
    [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {l : D ⥤ E} {u : E ⥤ D} (adj : l ⊣ u)
    (α : L ⋙ G ≅ F ⋙ l) (β : U ⋙ F ≅ G ⋙ u) : L ⊣ U :=
  adj.restrictFullyFaithful (Functor.FullyFaithful.ofFullyFaithful F)
    (Functor.FullyFaithful.ofFullyFaithful G) α.symm β.symm

private theorem transportedAdjunction_unit
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : A ⥤ D} {G : B ⥤ E}
    [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {l : D ⥤ E} {u : E ⥤ D} (adj : l ⊣ u)
    (α : L ⋙ G ≅ F ⋙ l) (β : U ⋙ F ≅ G ⋙ u) (X : A) :
    F.map ((transportedAdjunction adj α β).unit.app X) =
      adj.unit.app (F.obj X) ≫ u.map (α.inv.app X) ≫ β.inv.app (L.obj X) :=
  Adjunction.map_restrictFullyFaithful_unit_app adj
    (Functor.FullyFaithful.ofFullyFaithful F) (Functor.FullyFaithful.ofFullyFaithful G)
    α.symm β.symm X

private theorem transportedAdjunction_hom
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : A ⥤ D} {G : B ⥤ E}
    [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {l : D ⥤ E} {u : E ⥤ D} (adj : l ⊣ u)
    (α : L ⋙ G ≅ F ⋙ l) (β : U ⋙ F ≅ G ⋙ u)
    (X : A) (Y : B) (f : L.obj X ⟶ Y) :
    F.map ((transportedAdjunction adj α β).homEquiv X Y f) ≫ β.hom.app Y =
      adj.homEquiv _ _ (α.inv.app X ≫ G.map f) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, transportedAdjunction_unit]
  simp only [Category.assoc]
  erw [← β.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app, Category.comp_id, Adjunction.homEquiv_unit,
    Functor.map_comp]
  rfl

attribute [local irreducible] transportedAdjunction

private theorem transportedAdjunction_unit_diagram
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : A ⥤ D} {G : B ⥤ E}
    [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    {l : D ⥤ E} {u : E ⥤ D} (adj : l ⊣ u)
    (α : L ⋙ G ≅ F ⋙ l) (β : U ⋙ F ≅ G ⋙ u)
    (X T : A) (Y : B) (P Z : D) (V W : E)
    (η : X ⟶ T) (r : U.obj Y ⟶ T) (ε : L.obj X ⟶ Y)
    (p : F.obj X ⟶ P) (q : G.obj Y ⟶ W) (c : V ⟶ W)
    (e : l.obj P ⟶ V) (b : u.obj W ⟶ Z) (t : F.obj T ⟶ Z) [Mono t]
    (hβ : β.hom.app Y ≫ u.map q ≫ b = F.map r ≫ t)
    (hε : G.map ε ≫ q = α.hom.app X ≫ l.map p ≫ e ≫ c)
    (hη : p ≫ adj.unit.app P ≫ u.map e ≫ u.map c ≫ b = F.map η ≫ t) :
    (transportedAdjunction adj α β).unit.app X ≫ U.map ε ≫ r = η := by
  apply F.map_injective
  apply (cancel_mono t).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [transportedAdjunction_unit, Category.assoc, Category.assoc, ← hβ]
  erw [← β.inv.naturality_assoc ε]
  simp only [Functor.comp_map, Iso.inv_hom_id_app_assoc]
  erw [← u.map_comp_assoc (G.map ε) q, hε]
  simp only [Functor.map_comp, Category.assoc]
  erw [← u.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  erw [← adj.unit.naturality_assoc p]
  simpa only [Functor.id_map] using hη

-- The proof transports universal localization data and its normalization diagrams.
private theorem derivedTransport
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (eR : A ≌ D) (eS0 : B ≌ E)
    [eR.functor.Additive] [eS0.functor.Additive]
    (L : A ⥤ B) (U : B ⥤ A) [L.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (l : D ⥤ E) (u : E ⥤ D) [hadd : l.Additive] [u.Additive]
    [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    (adjI : L ⊣ U) (adjS : l ⊣ u)
    (F : DerivedCategory D ⥤ DerivedCategory E)
    (εh : DerivedCategory.Qh ⋙ F ⟶ l.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hderived : F.IsLeftDerivedFunctor εh (HomotopyCategory.quasiIso D (.up ℤ)))
    (K : CochainComplex D ℤ → Prop)
    (hcomputes : ∀ P, K P → IsIso (εh.app ((HomotopyCategory.quotient D (.up ℤ)).obj P)))
    (adjD : F ⊣ u.mapDerivedCategory)
    (hunitAll : ∀ P : CochainComplex D ℤ,
      adjD.unit.app (DerivedCategory.Q.obj P) ≫
        u.mapDerivedCategory.map (εh.app ((HomotopyCategory.quotient D (.up ℤ)).obj P)) ≫
          u.mapDerivedCategoryFactors.hom.app ((l.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((adjS.mapHomologicalComplex (.up ℤ)).unit.app P))
    (restriction : U ⋙ eR.functor ≅ eS0.functor ⋙ u)
    (extension : L ⋙ eS0.functor ≅ eR.functor ⋙ l)
    (htranspose : ∀ (M : A) (N : B) (f : L.obj M ⟶ N),
      eR.functor.map (adjI.homEquiv M N f) ≫ restriction.hom.app N =
        adjS.homEquiv _ _ (extension.inv.app M ≫ eS0.functor.map f)) :
    ∃ (LF : DerivedCategory A ⥤ DerivedCategory B)
      (ε : DerivedCategory.Q ⋙ LF ⟶ L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
      LF.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ)) ∧
      (∀ P, K ((eR.functor.mapHomologicalComplex (.up ℤ)).obj P) → IsIso (ε.app P)) ∧
      ∃ ad : LF ⊣ U.mapDerivedCategory,
      (∀ P : CochainComplex A ℤ,
        ad.unit.app (DerivedCategory.Q.obj P) ≫ U.mapDerivedCategory.map (ε.app P) ≫
          U.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((adjI.mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
      ∃ dr : U.mapDerivedCategory ⋙ eR.functor.mapDerivedCategory ≅
        eS0.functor.mapDerivedCategory ⋙ u.mapDerivedCategory,
      (dr = Functor.mapDerivedCategoryCompIso U eR.functor ≪≫
        Functor.mapDerivedCategoryNatIso restriction ≪≫
        (Functor.mapDerivedCategoryCompIso eS0.functor u).symm) ∧
      ∃ de : LF ⋙ eS0.functor.mapDerivedCategory ≅ eR.functor.mapDerivedCategory ⋙ F,
      (∀ P : CochainComplex A ℤ,
        eS0.functor.mapDerivedCategory.map (ε.app P) ≫
          eS0.functor.mapDerivedCategoryFactors.hom.app
            ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) =
        de.hom.app (DerivedCategory.Q.obj P) ≫
          F.map (eR.functor.mapDerivedCategoryFactors.hom.app P) ≫
            εh.app ((HomotopyCategory.quotient D (.up ℤ)).obj
              ((eR.functor.mapHomologicalComplex (.up ℤ)).obj P))) ∧
      ∀ (M : DerivedCategory A) (N : DerivedCategory B) (f : LF.obj M ⟶ N),
        eR.functor.mapDerivedCategory.map (ad.homEquiv M N f) ≫ dr.hom.app N =
          adjD.homEquiv _ _ (de.inv.app M ≫ eS0.functor.mapDerivedCategory.map f) := by
  classical
  let ER := eR.functor
  let ES := eS0.functor
  let ERc := ER.mapHomologicalComplex (.up ℤ)
  let ESc := ES.mapHomologicalComplex (.up ℤ)
  let EX := L.mapHomologicalComplex (.up ℤ)
  let lc := l.mapHomologicalComplex (.up ℤ)
  have : ERc.IsEquivalence :=
    inferInstanceAs (eR.mapHomologicalComplex (.up ℤ)).functor.IsEquivalence
  let ERd := ER.mapDerivedCategory
  let ESd := ES.mapDerivedCategory
  let eS := ESd.asEquivalence
  let LF0 := transportedLeft ERd F eS
  let de : LF0 ⋙ ESd ≅ ERd ⋙ F :=
    transportedLeftIso ERd F eS
  let dr : U.mapDerivedCategory ⋙ ERd ≅
      ESd ⋙ u.mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso U ER ≪≫
      Functor.mapDerivedCategoryNatIso restriction ≪≫
      (Functor.mapDerivedCategoryCompIso ES (u)).symm
  let ce : EX ⋙ ESc ≅ ERc ⋙ lc :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ ES)) _).symm ≪≫
      NatIso.mapHomologicalComplex extension _ ≪≫
      Functor.mapHomologicalComplexCompIso (Iso.refl (ER ⋙ l)) _
  let fe : (EX ⋙ DerivedCategory.Q) ⋙ ESd ≅ ERc ⋙ (lc ⋙ DerivedCategory.Q) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EX ES.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ce DerivedCategory.Q ≪≫
      Functor.associator _ _ _
  let q := HomotopyCategory.quotient
    (D) (.up ℤ)
  let ec : DerivedCategory.Q ⋙ F ⟶ lc ⋙ DerivedCategory.Q :=
    { app := fun P ↦ εh.app (q.obj P)
      naturality := fun P P' f ↦ εh.naturality (q.map f) }
  let δ : (DerivedCategory.Q ⋙ LF0) ⋙ ESd ⟶ (EX ⋙ DerivedCategory.Q) ⋙ ESd :=
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft DerivedCategory.Q de.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ER.mapDerivedCategoryFactors.hom F ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft ERc ec ≫ fe.inv
  let W := (Functor.whiskeringRight
    (CochainComplex (A) ℤ)
    (DerivedCategory B) _).obj ESd
  let ε : DerivedCategory.Q ⋙ LF0 ⟶ EX ⋙ DerivedCategory.Q := W.preimage δ
  have hε : Functor.whiskerRight ε ESd = δ := W.map_preimage δ
  refine ⟨LF0, ε, ?_, ?_, ?_⟩
  · apply (Functor.isLeftDerivedFunctor_iff_isRightKanExtension LF0 ε _).mpr
    have hu := hderived
    have := Functor.IsLeftDerivedFunctor.isRightKanExtension
      F εh
        (HomotopyCategory.quasiIso
          (D) (.up ℤ))
    have := ModuleCat.kan_precomp_full q DerivedCategory.Qh _ F εh
    have hec : F.IsRightKanExtension ec := by
      let i := DerivedCategory.quotientCompQhIso
        (D)
      let j : q ⋙ (l.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) ≅ lc ⋙ DerivedCategory.Q :=
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (l.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft lc (DerivedCategory.quotientCompQhIso _)
      let b := Functor.whiskerRight i.hom F ≫ ec
      have hb : F.IsRightKanExtension b := by
        apply (Functor.isRightKanExtension_iff_of_iso₂ _ b j (Iso.refl _) ?_).mp this
        ext P
        dsimp [b, j, i, ec]
        change 𝟙 _ ≫ F.map (𝟙 _) ≫ εh.app (q.obj P) =
          (𝟙 _ ≫ εh.app (q.obj P)) ≫ 𝟙 _ ≫
            DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ 𝟙 _
        erw [Functor.map_id, Functor.map_id]
        simp only [Category.id_comp, Category.comp_id]
        erw [Category.comp_id]
      apply (Functor.isRightKanExtension_iff_postcomp₁
        (𝟭 _) ((Functor.rightUnitor (q ⋙ DerivedCategory.Qh)) ≪≫ i) ec).mpr
      apply Functor.isRightKanExtension_of_iso
        (Functor.leftUnitor F).symm b _
      ext P
      simp only [Functor.comp_obj, Iso.symm_hom, Iso.trans_hom,
        Functor.whiskerRight_comp, Category.assoc, NatTrans.comp_app, Functor.id_obj,
        Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_inv_app,
        Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Functor.map_id,
        Category.id_comp]
      erw [Category.id_comp]
      rfl
    apply kan_transport ERc ESd ERd DerivedCategory.Q DerivedCategory.Q
      (EX ⋙ DerivedCategory.Q) (lc ⋙ DerivedCategory.Q) LF0 F
      ER.mapDerivedCategoryFactors fe de ε ec
    intro P
    have hh := NatTrans.congr_app hε P
    change ESd.map (ε.app P) = _ at hh
    rw [hh]
    dsimp [δ]
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  · intro P hP
    have hc := hcomputes (ERc.obj P) hP
    have : IsIso (ec.app (ERc.obj P)) := hc
    have : IsIso (ESd.map (ε.app P)) := by
      rw [← Functor.whiskerRight_app, hε]
      dsimp [δ]
      exact inferInstance
    exact isIso_of_reflects_iso (ε.app P) ESd
  · let ad := transportedAdjunction adjD de dr
    refine ⟨ad, ?_, dr, rfl, de, ?_, ?_⟩
    · intro P
      let RI := U
      let RS := u
      let RSc := RS.mapHomologicalComplex (.up ℤ)
      let rC := (Functor.mapHomologicalComplexCompIso (Iso.refl (RI ⋙ ER)) (.up ℤ)).symm ≪≫
        NatIso.mapHomologicalComplex restriction (.up ℤ) ≪≫
        Functor.mapHomologicalComplexCompIso (Iso.refl (ES ⋙ RS)) (.up ℤ)
      have hOrd (M : A) :
          ER.map ((adjI).unit.app M) ≫
              restriction.hom.app (L.obj M) =
            adjS.unit.app (ER.obj M) ≫
              RS.map (extension.inv.app M) := by
        have h := htranspose M (L.obj M) (𝟙 _)
        simp only [Adjunction.homEquiv_unit, Functor.map_id] at h
        erw [Category.comp_id, Category.comp_id] at h
        exact h
      have hOrdC : ERc.map (((adjI).mapHomologicalComplex
            (.up ℤ)).unit.app P) ≫ rC.hom.app (EX.obj P) =
          (adjS.mapHomologicalComplex (.up ℤ)).unit.app (ERc.obj P) ≫
            RSc.map (ce.inv.app P) := by
        ext n : 1
        dsimp only [ERc, RSc, ER, RS, RI, EX, rC, ce,
          Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
          NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplex,
          Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
          NatTrans.comp_app, HomologicalComplex.comp_f]
        simp only [Adjunction.mapHomologicalComplex_unit_app_f, Iso.refl_hom,
          Iso.refl_inv, NatTrans.id_app]
        erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
        exact hOrd (P.X n)
      have hr := derived_square_fac RI ER ES RS restriction (EX.obj P)
      change dr.hom.app _ ≫ _ ≫ _ = _ ≫ _ ≫ DerivedCategory.Q.map
        (rC.hom.app (EX.obj P)) at hr
      have hs := hunitAll (ERc.obj P)
      have hd := NatTrans.congr_app hε P
      change ESd.map (ε.app P) = _ at hd
      have hfe : fe.hom.app P = ES.mapDerivedCategoryFactors.hom.app (EX.obj P) ≫
          DerivedCategory.Q.map (ce.hom.app P) := by
        dsimp only [fe, Iso.trans_hom, NatTrans.comp_app,
          Functor.associator_hom_app, Functor.associator_inv_app,
          Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
          Functor.whiskerLeft_app, Functor.whiskerRight_app]
        simp only [Category.id_comp, Category.comp_id]
        erw [Category.id_comp]
      have hfe' : fe.inv.app P ≫ ES.mapDerivedCategoryFactors.hom.app (EX.obj P) =
          DerivedCategory.Q.map (ce.inv.app P) := by
        apply (cancel_epi (fe.hom.app P)).mp
        simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
        rw [hfe]
        simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
        erw [Functor.map_id, Category.comp_id]
      let r := U.mapDerivedCategoryFactors.hom.app (EX.obj P)
      let t := ER.mapDerivedCategoryFactors.hom.app
        ((RI.mapHomologicalComplex (.up ℤ)).obj (EX.obj P)) ≫
          DerivedCategory.Q.map (rC.hom.app (EX.obj P))
      have hcomparison : ESd.map (ε.app P) ≫ ES.mapDerivedCategoryFactors.hom.app
          (EX.obj P) = de.hom.app (DerivedCategory.Q.obj P) ≫
            F.map (ER.mapDerivedCategoryFactors.hom.app P) ≫
              ec.app (ERc.obj P) ≫ DerivedCategory.Q.map (ce.inv.app P) := by
        rw [hd]
        dsimp only [δ, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, Functor.associator_hom_app,
          Functor.associator_inv_app]
        simp only [Category.id_comp, Category.assoc]
        rw [hfe']
      have hnormal : ER.mapDerivedCategoryFactors.hom.app P ≫
          adjD.unit.app (DerivedCategory.Q.obj (ERc.obj P)) ≫
            (u.mapDerivedCategory).map (ec.app (ERc.obj P)) ≫
              (u.mapDerivedCategory).map
                (DerivedCategory.Q.map (ce.inv.app P)) ≫
                  RS.mapDerivedCategoryFactors.hom.app (ESc.obj (EX.obj P)) =
          ERd.map (DerivedCategory.Q.map
            (((adjI).mapHomologicalComplex (.up ℤ)).unit.app P)) ≫
              t := by
        erw [RS.mapDerivedCategoryFactors.hom.naturality (ce.inv.app P)]
        dsimp only [Functor.comp_map]
        have hs' := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map (RSc.map (ce.inv.app P))) hs
        simp only [Category.assoc] at hs'
        erw [hs', ← DerivedCategory.Q.map_comp, ← hOrdC, DerivedCategory.Q.map_comp]
        erw [← ER.mapDerivedCategoryFactors.hom.naturality_assoc
          (((adjI).mapHomologicalComplex (.up ℤ)).unit.app P)]
        rfl
      exact transportedAdjunction_unit_diagram adjD de dr
        (DerivedCategory.Q.obj P) _ (DerivedCategory.Q.obj (EX.obj P)) _ _ _ _
        (DerivedCategory.Q.map
          (((adjI).mapHomologicalComplex (.up ℤ)).unit.app P))
        r (ε.app P) (ER.mapDerivedCategoryFactors.hom.app P)
        (ES.mapDerivedCategoryFactors.hom.app (EX.obj P))
        (DerivedCategory.Q.map (ce.inv.app P)) (ec.app (ERc.obj P))
        (RS.mapDerivedCategoryFactors.hom.app (ESc.obj (EX.obj P))) t
        hr hcomparison hnormal
    · intro P
      have hh := NatTrans.congr_app hε P
      dsimp [δ] at hh
      rw [hh]
      simp only [Category.id_comp]
      have hfe : fe.hom.app P = ES.mapDerivedCategoryFactors.hom.app (EX.obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) := by
        dsimp [fe, ce]
        simp only [Functor.map_comp, Category.comp_id, Category.id_comp,
          NatIso.cancel_natIso_hom_left, Functor.comp_obj]
        change DerivedCategory.Q.map (𝟙 _) ≫ _ ≫ DerivedCategory.Q.map (𝟙 _) = _
        simp
      rw [← hfe]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app, Category.comp_id]
    · intro M N f
      exact transportedAdjunction_hom adjD de dr M N f

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
  {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{u}) R)]
  [HasDerivedCategory.{w} (Mod (Sheaf J AddCommGrpCat.{u}) S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

omit [HasDerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) R)]
  [HasDerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) S)] in
private theorem sectionPair_unit_good
    (φ : sectionRingSheaf J R ⟶ sectionRingSheaf J S)
    (s : SheafOfModules.ScalarDerivedPair φ)
    (P : CochainComplex (SheafOfModules.scalarModules J (sectionRingSheaf J R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R) P)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := sectionRingSheaf J R) (P.X n)) :
    s.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (SheafOfModules.scalarDerivedRestriction φ).map
          (SheafOfModules.scalarPairComplexComparison s.extension s.extension_additive
            s.derived s.counit P) ≫
        (SheafOfModules.scalarRestriction φ).mapDerivedCategoryFactors.hom.app
          ((s.extension.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let am := s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)
  have hn := s.normalization P hP hflat _ (am.unit.app P)
  have ht : SheafOfModules.scalarChainTranspose φ s.extension s.extension_additive
      s.ordinaryAdjunction P _ (am.unit.app P) = 𝟙 _ := by
    exact (am.homEquiv _ _).symm_apply_eq.mpr (am.homEquiv_id P).symm
  rw [ht, DerivedCategory.Q.map_id, Category.comp_id] at hn
  have hh := congrArg (s.adjunction.homEquiv _ _) hn
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at hh
  change _ = _ at hh
  erw [← Category.assoc, ← hh, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

omit [HasDerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) R)]
  [HasDerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) S)] in
private theorem sectionPair_unit_all
    (φ : sectionRingSheaf J R ⟶ sectionRingSheaf J S)
    (s : SheafOfModules.ScalarDerivedPair φ) :
    ∀ (P : CochainComplex (SheafOfModules.scalarModules J (sectionRingSheaf J R)) ℤ),
    s.adjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (SheafOfModules.scalarDerivedRestriction φ).map
          (s.counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (SheafOfModules.scalarRestriction φ).mapDerivedCategoryFactors.hom.app
          ((s.extension.mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map ((s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let E := s.extension.mapHomologicalComplex (.up ℤ)
  let RC := (SheafOfModules.scalarRestriction φ).mapHomologicalComplex (.up ℤ)
  let RD := SheafOfModules.scalarDerivedRestriction φ
  let q := HomotopyCategory.quotient
    (SheafOfModules.scalarModules J (sectionRingSheaf J R)) (.up ℤ)
  let ec : DerivedCategory.Q ⋙ s.derived ⟶ E ⋙ DerivedCategory.Q :=
    { app := fun P ↦ s.counit.app (q.obj P)
      naturality := fun _ _ f ↦ s.counit.naturality (q.map f) }
  let θ₁ : DerivedCategory.Q ⟶ (E ⋙ RC) ⋙ DerivedCategory.Q :=
    DerivedCategory.Q.rightUnitor.inv ≫ Functor.whiskerLeft DerivedCategory.Q s.adjunction.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ec RD ≫
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft E
        (SheafOfModules.scalarRestriction φ).mapDerivedCategoryFactors.hom ≫
      (Functor.associator _ _ _).inv
  let θ₂ : DerivedCategory.Q ⟶ (E ⋙ RC) ⋙ DerivedCategory.Q :=
    DerivedCategory.Q.leftUnitor.inv ≫
      Functor.whiskerRight (s.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).unit
        DerivedCategory.Q
  intro P
  obtain ⟨L, f, hL, hflat, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := sectionRingSheaf J R) P
  have hgood : θ₁.app L = θ₂.app L := by
    have hfsite (n : ℤ) : SheafOfModules.IsFlatOnSite
        (R := sectionRingSheaf J R) (L.X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (sectionRingSheaf J R) _).symm (hflat n)
    have h := sectionPair_unit_good J φ s L hL hfsite
    have he : SheafOfModules.scalarPairComplexComparison s.extension s.extension_additive
        s.derived s.counit L = ec.app L := by
      dsimp only [SheafOfModules.scalarPairComplexComparison, ec]
      change s.derived.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
      simp
      rfl
    rw [he] at h
    simpa [θ₁, θ₂] using h
  have : QuasiIso f := hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  have hh : θ₁.app P = θ₂.app P := by
    apply (cancel_epi (DerivedCategory.Q.map f)).mp
    rw [θ₁.naturality, hgood, ← θ₂.naturality]
  simpa [θ₁, θ₂] using hh

-- Localization uses the equivalence API; do not unfold its section reconstruction.
attribute [local irreducible] sectionModuleEquivalence Mod.extendScalars Mod.comap

-- The proof compares several localization factorization isomorphisms simultaneously.
/-- Transport a normalized scalar derived pair through the exact section equivalences.
The input squares are ordinary adjunction squares; this result concerns localization only.
Source: Stacks Project, Derived Categories, Tag 09T5; Cohomology on Sites, Tags 06YY,
07A6 (auxiliary; not a blueprint node).
Proof:
1. Localize the two exact section equivalences and the restriction square. Define the
internal derived extension by conjugating the given universal derived extension with
these equivalences. Define its comparison by the termwise extension square and the
localization factorization isomorphisms.
2. Right Kan extensions are invariant under equivalences of source, localization target,
and value category. Thus the transported comparison is universal. Its component is an
isomorphism whenever the original component is, in particular on sectionwise K-flat
complexes.
3. Conjugate the given derived adjunction. Its extension square is the inverse mate of
the localized restriction square. The ordinary transpose identity identifies the
ordinary mate. The normalized representative formula for the scalar pair identifies
these mates on flat-term K-flat resolutions. Naturality along their quasi-isomorphisms
then gives the unit identity on every complex. The same unit identity determines the
Hom transpose on arbitrary derived objects. -/
theorem derived_section_scalar_transport
    (φ : sectionRingSheaf J R ⟶ sectionRingSheaf J S)
    (sectionPair : SheafOfModules.ScalarDerivedPair φ)
    (restriction : Mod.comap a ⋙ (sectionModuleEquivalence J R).functor ≅
      (sectionModuleEquivalence J S).functor ⋙ SheafOfModules.scalarRestriction φ)
    (extension : Mod.extendScalars a ⋙ (sectionModuleEquivalence J S).functor ≅
      (sectionModuleEquivalence J R).functor ⋙ sectionPair.extension)
    (htranspose : ∀ (M : Mod (Sheaf J AddCommGrpCat.{u}) R)
      (N : Mod (Sheaf J AddCommGrpCat.{u}) S) (f : (Mod.extendScalars a).obj M ⟶ N),
      (sectionModuleEquivalence J R).functor.map
          ((Mod.extendRestrictAdjunction a).homEquiv M N f) ≫ restriction.hom.app N =
        sectionPair.ordinaryAdjunction.homEquiv _ _
          (extension.inv.app M ≫ (sectionModuleEquivalence J S).functor.map f)) :
  -- The internal unbounded derived scalar extension.
  ∃ internalDerived : (DerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) R) ⥤
    DerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) S)),
  -- Its comparison on the actual complexes.
  ∃ internalCounit : (DerivedCategory.Q ⋙ internalDerived ⟶
    (Mod.extendScalars a).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
  -- This is the universal left derived functor, not an arbitrary left adjoint.
  (internalDerived.IsLeftDerivedFunctor internalCounit
    (HomologicalComplex.quasiIso (Mod (Sheaf J AddCommGrpCat.{u}) R) (.up ℤ))) ∧
  -- K-flat complexes compute the internal universal pair. K-flatness is transported
  -- by the recorded equivalence, as in internal_section_tensor_comparison.
  (∀ (P : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
        IsIso (internalCounit.app P)) ∧
  -- The specified internal derived extension/exact restriction adjunction.
  ∃ internalAdjunction : (internalDerived ⊣ (Mod.comap a).mapDerivedCategory),
  -- The internal derived unit is induced by the specified ordinary internal unit.
  -- This pins the derived adjunction independently of section reconstruction.
  (∀ (P : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ),
    internalAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
        (Mod.comap a).mapDerivedCategory.map (internalCounit.app P) ≫
        (Mod.comap a).mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P)) ∧
  -- The termwise equivalences identify derived restrictions.
  ∃ derivedRestriction : ((Mod.comap a).mapDerivedCategory ⋙
      (sectionModuleEquivalence J R).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J S).functor.mapDerivedCategory ⋙
      SheafOfModules.scalarDerivedRestriction (φ)),
  -- Restriction comparison is precisely localization of the ordinary one.
  (derivedRestriction =
    Functor.mapDerivedCategoryCompIso (Mod.comap a)
      (sectionModuleEquivalence J R).functor ≪≫
    Functor.mapDerivedCategoryNatIso restriction ≪≫
    (Functor.mapDerivedCategoryCompIso (sectionModuleEquivalence J S).functor
      (SheafOfModules.scalarRestriction (φ))).symm) ∧
  -- The comparison of the universal derived extensions.
  ∃ derivedExtension : (internalDerived ⋙
      (sectionModuleEquivalence J S).functor.mapDerivedCategory ≅
    (sectionModuleEquivalence J R).functor.mapDerivedCategory ⋙ sectionPair.derived),
  -- On flat-term K-flat representatives, this is the localized termwise comparison.
  (∀ (P : CochainComplex (Mod (Sheaf J AddCommGrpCat.{u}) R) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients (R := sectionRingSheaf J R)
      (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := sectionRingSheaf J R)
      ((sectionModuleEquivalence J R).functor.obj (P.X n))) →
    (sectionModuleEquivalence J S).functor.mapDerivedCategory.map (internalCounit.app P) ≫
        (sectionModuleEquivalence J S).functor.mapDerivedCategoryFactors.hom.app
          (((Mod.extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex extension (.up ℤ)).hom.app P) =
      derivedExtension.hom.app (DerivedCategory.Q.obj P) ≫
        sectionPair.derived.map
          ((sectionModuleEquivalence J R).functor.mapDerivedCategoryFactors.hom.app P) ≫
        SheafOfModules.scalarPairComplexComparison sectionPair.extension
          sectionPair.extension_additive sectionPair.derived sectionPair.counit
          (((sectionModuleEquivalence J R).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- Agreement of the specified derived transposes includes derived units and counits.
  ∀ (M : DerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) R))
      (N : DerivedCategory (Mod (Sheaf J AddCommGrpCat.{u}) S)) (f : internalDerived.obj M ⟶ N),
      (sectionModuleEquivalence J R).functor.mapDerivedCategory.map
          (internalAdjunction.homEquiv M N f) ≫ derivedRestriction.hom.app N =
        sectionPair.adjunction.homEquiv _ _ (derivedExtension.inv.app M ≫
          (sectionModuleEquivalence J S).functor.mapDerivedCategory.map f) := by
  classical
  let s := sectionPair
  let q := HomotopyCategory.quotient
    (SheafOfModules.scalarModules J (sectionRingSheaf J R)) (.up ℤ)
  have he (P : CochainComplex
      (SheafOfModules.scalarModules J (sectionRingSheaf J R)) ℤ) :
      SheafOfModules.scalarPairComplexComparison s.extension s.extension_additive
        s.derived s.counit P = s.counit.app (q.obj P) := by
    dsimp only [SheafOfModules.scalarPairComplexComparison]
    change s.derived.map (𝟙 _) ≫ _ ≫ 𝟙 _ = _
    simp only [Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  have hc (P : CochainComplex
      (SheafOfModules.scalarModules J (sectionRingSheaf J R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients
        (R := sectionRingSheaf J R) P) : IsIso (s.counit.app (q.obj P)) := by
    rw [← he]
    exact s.computes P hP
  obtain ⟨LF, ε, hLF, hcalc, ad, hunit, dr, hdr, de, hrep, hhom⟩ :=
    derivedTransport (sectionModuleEquivalence J R) (sectionModuleEquivalence J S)
      (Mod.extendScalars a) (Mod.comap a) s.extension (SheafOfModules.scalarRestriction φ)
      (Mod.extendRestrictAdjunction a) s.ordinaryAdjunction s.derived s.counit s.isLeftDerived
      (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
        (R := sectionRingSheaf J R) P) hc s.adjunction
      (sectionPair_unit_all J φ s) restriction extension htranspose
  refine ⟨LF, ε, hLF, hcalc, ad, hunit, dr, hdr, de, ?_, hhom⟩
  intro P hP hflat
  rw [he]
  exact hrep P

end CategoryTheory.InternalAbelianSheafModule
