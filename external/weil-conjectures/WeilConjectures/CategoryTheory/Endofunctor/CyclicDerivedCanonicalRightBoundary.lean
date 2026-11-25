/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomData
public import WeilConjectures.CategoryTheory.KInjectiveExactSquare.KInjectiveExactSquareComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.CategoryTheory.Endofunctor.CyclicDerivedHomExactSequence
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift

/-! # Cyclic Hom functoriality for the canonical total right derived functor

Source: Stacks Project, Derived Categories, Tags 070I, 070K and 070Y; the
right-derived comparison step in the native compact-support transport argument.
(blueprint: lem-sf-cyclic-derived-canonical-right-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open CategoryTheory.Endofunctor.IsoAlgebra

private theorem conjugation_transport
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (P : A ⥤ A) (R : B ⥤ B) (H : A ⥤ B)
    [P.CommShift ℤ] [R.CommShift ℤ] [H.CommShift ℤ]
    (β : H ⋙ R ≅ P ⋙ H) [NatTrans.CommShift β.hom ℤ]
    {XM XN : A} {YM YN : B}
    (θM : P.obj XM ≅ XM) (θN : P.obj XN ≅ XN)
    (ψM : R.obj YM ≅ YM) (ψN : R.obj YN ≅ YN)
    (αM : YM ≅ H.obj XM) (αN : YN ≅ H.obj XN)
    (hM : R.map αM.hom ≫ β.hom.app XM ≫ H.map θM.hom = ψM.hom ≫ αM.hom)
    (hN : R.map αN.hom ≫ β.hom.app XN ≫ H.map θN.hom = ψN.hom ≫ αN.hom)
    (r : ℤ) (u : XM ⟶ XN⟦r⟧) :
    αM.hom ≫ H.map (θM.inv ≫ P.map u ≫ (P.commShiftIso r).hom.app XN ≫
        θN.hom⟦r⟧') ≫ (H.commShiftIso r).hom.app XN ≫ αN.inv⟦r⟧' =
      ψM.inv ≫ R.map (αM.hom ≫ H.map u ≫ (H.commShiftIso r).hom.app XN ≫
        αN.inv⟦r⟧') ≫ (R.commShiftIso r).hom.app YN ≫ ψN.hom⟦r⟧' := by
  have hMi : αM.hom ≫ H.map θM.inv =
      ψM.inv ≫ R.map αM.hom ≫ β.hom.app XM := by
    have h := congrArg (fun f ↦ ψM.inv ≫ f ≫ H.map θM.inv) hM
    simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id, H.map_id,
      Iso.inv_hom_id_assoc] at h
    erw [Category.comp_id] at h
    exact h.symm
  have hNi : β.hom.app XN ≫ H.map θN.hom ≫ αN.inv =
      R.map αN.inv ≫ ψN.hom := by
    have h := congrArg (fun f ↦ R.map αN.inv ≫ f ≫ αN.inv) hN
    simpa only [Category.assoc, ← R.map_comp_assoc, Iso.inv_hom_id, R.map_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id] using h
  have hb := NatTrans.shift_app_comm β.hom r XN
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hb
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  have ht := congrArg (fun f ↦ f⟦r⟧') hNi
  simp only [Functor.map_comp] at ht
  simp only [H.map_comp, R.map_comp, Category.assoc]
  rw [reassoc_of% hMi, ← reassoc_of% (β.hom.naturality u)]
  rw [H.commShiftIso_hom_naturality_assoc, ← reassoc_of% hb, ht]
  rw [← R.commShiftIso_hom_naturality_assoc]

private theorem action_apply
    {C : Type*} [Category C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
    [HasDerivedCategory C] [HasDerivedCategory (IsoAlgebra F)]
    (M N : DerivedCategory (IsoAlgebra F)) (r : ℤ) (v : CyclicDerivedHom F M N r) :
    cyclicDerivedHomAction F M N r v =
      ((cyclicDerivedStructure F).inv.app M ≫ F.mapDerivedCategory.map v) ≫
        ((F.mapDerivedCategory.commShiftIso r).hom.app
            ((IsoAlgebra.forget F).mapDerivedCategory.obj N) ≫
          ((cyclicDerivedStructure F).hom.app N)⟦r⟧') := rfl

private theorem model_transport
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    [HasShift B ℤ] [HasShift E ℤ]
    (U : A ⥤ B) (V : C ⥤ E) (J J' : A ⥤ C) (T T' : B ⥤ E)
    [T.CommShift ℤ] [T'.CommShift ℤ]
    (a : J ≅ J') (b : T ≅ T') [NatTrans.CommShift b.hom ℤ]
    (α : J' ⋙ V ≅ U ⋙ T') (M N : A) (r : ℤ) (v : U.obj M ⟶ (U.obj N)⟦r⟧) :
    let β := Functor.isoWhiskerRight a V ≪≫ α ≪≫ Functor.isoWhiskerLeft U b.symm
    β.hom.app M ≫ T.map v ≫ (T.commShiftIso r).hom.app (U.obj N) ≫
        (β.inv.app N)⟦r⟧' =
      V.map (a.hom.app M) ≫
        (α.hom.app M ≫ T'.map v ≫ (T'.commShiftIso r).hom.app (U.obj N) ≫
          (α.inv.app N)⟦r⟧') ≫ (V.map (a.inv.app N))⟦r⟧' := by
  dsimp only
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (b.inv.naturality v), reassoc_of% (NatTrans.shift_app_comm b.hom r
    (U.obj N))]
  simp only [Iso.inv_hom_id_app_assoc]

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  (G : D ⥤ D) [G.Additive] [G.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]
  [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions (IsoAlgebra F)]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L]
  (e : L ⋙ G ≅ F ⋙ L)

omit [IsGrothendieckAbelian.{v'} D] in
private theorem action_change_endpoints
    {M N M' N' : DerivedCategory (IsoAlgebra G)} (a : M' ≅ M) (c : N' ≅ N)
    (r : ℤ) (v : CyclicDerivedHom G M N r) :
    (forget G).mapDerivedCategory.map a.hom ≫ cyclicDerivedHomAction G M N r v ≫
        ((forget G).mapDerivedCategory.map c.inv)⟦r⟧' =
      cyclicDerivedHomAction G M' N' r
        ((forget G).mapDerivedCategory.map a.hom ≫ v ≫
          ((forget G).mapDerivedCategory.map c.inv)⟦r⟧') := by
  let P := G.mapDerivedCategory
  let V := (forget G).mapDerivedCategory
  let θ := cyclicDerivedStructure G
  let β : (𝟭 _) ⋙ P ≅ P ⋙ (𝟭 _) :=
    Functor.leftUnitor P ≪≫ (Functor.rightUnitor P).symm
  have ha : P.map (V.map a.hom) ≫ β.hom.app (V.obj M) ≫
      (𝟭 _).map (θ.hom.app M) = θ.hom.app M' ≫ V.map a.hom := by
    simpa only [β, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
      Category.comp_id, Functor.id_map, Functor.comp_map, Functor.comp_obj, P, V, θ]
      using θ.hom.naturality a.hom
  have hc : P.map (V.map c.hom) ≫ β.hom.app (V.obj N) ≫
      (𝟭 _).map (θ.hom.app N) = θ.hom.app N' ≫ V.map c.hom := by
    simpa only [β, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
      Category.comp_id, Functor.id_map, Functor.comp_map, Functor.comp_obj, P, V, θ]
      using θ.hom.naturality c.hom
  have hβ : NatTrans.CommShift β.hom ℤ := by dsimp only [β, Iso.trans_hom]; infer_instance
  simpa only [action_apply, Functor.id_obj, Functor.id_map,
    Functor.commShiftIso_id_hom_app, Category.comp_id, Category.id_comp,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using
    conjugation_transport P P (𝟭 _) β (θ.app M) (θ.app N) (θ.app M') (θ.app N')
      (V.mapIso a) (V.mapIso c) ha hc r v

omit [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v'} D] in
private theorem standard_universal (T : C ⥤ D) [T.Additive]
    (H : DerivedCategory C ⥤ DerivedCategory D) :
    Function.Bijective (fun b : T.rightDerivedFunctor ⟶ H ↦
      T.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh b) := by
  constructor
  · intro a b hab
    exact T.rightDerivedFunctor.rightDerived_ext T.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ)) H a b hab
  · intro a
    exact ⟨T.rightDerivedFunctor.rightDerivedDesc T.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ)) H a,
        T.rightDerivedFunctor.rightDerived_fac T.rightDerivedFunctorUnit
          (HomotopyCategory.quasiIso C (.up ℤ)) H a⟩

/-- Cyclic graded-Hom functoriality does not depend on the implementation of total
right derivation when the forgetting comparison obeys the exact-square unit equation.

Proof: compare each arbitrary-resolution derived functor with the canonical total
right derived functor by the unique isomorphism preserving its unit. The isomorphism
on underlying categories commutes with shifts, since both units commute with shifts
and are invertible on K-injectives. Transport the supplied forgetting comparison back
along these two isomorphisms. Its unit equation identifies it with the unique comparison
used by cyclicDerivedHom_rightDerived_functorial. Apply that theorem with boundedness
transported along the native comparison. Naturality of the target boundary with respect
to the native comparison identifies the two output boundaries. Naturality and shift
compatibility of the underlying comparison cancel it from the degree-minus-one map.
Naturality of the cyclic structure identifies the endpoint-conjugated actions as
well. Additivity and degree-zero forgetting follow directly from the transport
formula and its zero-shift axiom. Thus all four functoriality components hold.

Source: Stacks Project, Derived Categories, Tags 070I, 070K and 070Y; the native
comparison step of lem-sf-native-exceptional-hom-transport-boundary.
(blueprint: lem-sf-cyclic-derived-canonical-right-boundary). -/
theorem cyclicDerivedCanonicalRight_functorial
    (α : (mapOfNatIso e).rightDerivedFunctor ⋙ (forget G).mapDerivedCategory ≅
      (forget F).mapDerivedCategory ⋙ L.rightDerivedFunctor)
    (hunit : ∀ I : CochainComplex (IsoAlgebra F) ℤ,
      KInjectiveExactSquare.leftUnit (mapOfNatIso e) L (forget F) (forget G) rfl
        (mapOfNatIso e).rightDerivedFunctor (mapOfNatIso e).rightDerivedFunctorUnit I ≫
          α.hom.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) =
      KInjectiveExactSquare.rightUnit L (forget F) L.rightDerivedFunctor
        L.rightDerivedFunctorUnit I)
    (b : CyclicDerivedHomBoundary F) (b' : CyclicDerivedHomBoundary G)
    (hb : CyclicDerivedHomBoundaryNormalized F b)
    (hb' : CyclicDerivedHomBoundaryNormalized G b')
    (hn : CyclicDerivedHomBoundaryNatural F b)
    (hn' : CyclicDerivedHomBoundaryNatural G b')
    : CyclicDerivedHomBoundaryFunctorial F G b b' (mapOfNatIso e).rightDerivedFunctor
        L.rightDerivedFunctor (fun r ↦ L.rightDerivedFunctor.commShiftIso r) α := by
  have hα (K : HomotopyCategory (IsoAlgebra F) (.up ℤ)) :
      (forget G).mapDerivedCategory.map ((mapOfNatIso e).rightDerivedFunctorUnit.app K) ≫
        α.hom.app (DerivedCategory.Qh.obj K) ≫
        L.rightDerivedFunctor.map ((forget F).mapDerivedCategoryFactorsh.hom.app K) =
      (forget G).mapDerivedCategoryFactorsh.hom.app
          (((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj K) ≫
        L.rightDerivedFunctorUnit.app (((forget F).mapHomotopyCategory (.up ℤ)).obj K) := by
    obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have h := hunit I
    dsimp only [KInjectiveExactSquare.leftUnit, KInjectiveExactSquare.rightUnit] at h
    have hid : (KInjectiveExactSquare.sourceIso (mapOfNatIso e) L
        (forget F) (forget G) rfl).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I) = 𝟙 _ := by
      change (𝟙 _) ≫ (𝟙 _) = _
      exact Category.id_comp _
    erw [hid, Functor.map_id, Category.id_comp] at h
    apply (cancel_epi ((forget G).mapDerivedCategoryFactorsh.inv.app
      (((mapOfNatIso e).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))).1
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← Category.assoc, ← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [Functor.map_id, Category.comp_id]
  let P := mapOfNatIso e
  let U := (forget F).mapDerivedCategory
  let V := (forget G).mapDerivedCategory
  let hP : ∀ K : CochainComplex (IsoAlgebra F) ℤ,
      ∃ (I : CochainComplex (IsoAlgebra F) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s := fun K ↦ by
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, s, hI, hs⟩
  let hC : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s := fun K ↦ by
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, s, hI, hs⟩
  obtain ⟨sP, sC, hsP, hsC, hf⟩ :=
    cyclicDerivedHom_rightDerived_functorial F G L e hP hC b b' hb hb' hn hn'
  let := sP
  let := sC
  have := hsP
  have := hsC
  obtain ⟨a, ha, _⟩ := P.rightDerivedFunctorOfQuasiIsoResolutions_unique hP
    P.rightDerivedFunctor P.rightDerivedFunctorUnit (standard_universal P)
  obtain ⟨c, hc, _⟩ := L.rightDerivedFunctorOfQuasiIsoResolutions_unique hC
    L.rightDerivedFunctor L.rightDerivedFunctorUnit (standard_universal L)
  have hη : NatTrans.CommShift L.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift L
  have hi : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
      obtain ⟨K, hK, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
      have := hK
      exact L.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hC K)
  have hcshift : NatTrans.CommShift c.hom ℤ := by
    have : NatTrans.CommShift
        (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC ≫
          Functor.whiskerLeft DerivedCategory.Qh c.hom) ℤ := by
      rw [hc]
      exact hη
    exact NatTrans.CommShift.of_comp_whiskerLeft_Qh
      (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC) c.hom
  let β := Functor.isoWhiskerRight a V ≪≫ α ≪≫ Functor.isoWhiskerLeft U c.symm
  have hβ : β = cyclicDerivedRightForgetComparison F G L e hP hC := by
    apply (Classical.choose_spec
      (exists_fixedPairDerivedForgetComparison F G L e hP hC)).2 β
    intro K
    change V.map ((P.rightDerivedFunctorOfQuasiIsoResolutionsUnit hP).app K) ≫
      β.hom.app (DerivedCategory.Qh.obj K) ≫
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC).map
        ((forget F).mapDerivedCategoryFactorsh.hom.app K) =
      (forget G).mapDerivedCategoryFactorsh.hom.app
        ((P.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map (𝟙 _) ≫ DerivedCategory.Qh.map (𝟙 _) ≫
          (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit hC).app
            (((forget F).mapHomotopyCategory (.up ℤ)).obj K)
    simp only [Functor.map_id, Category.id_comp]
    erw [Category.id_comp]
    dsimp only [β, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc]
    have hap := congr_app ha K
    have hcp := congr_app hc (((forget F).mapHomotopyCategory (.up ℤ)).obj K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hap hcp
    rw [← V.map_comp_assoc, hap]
    erw [← c.inv.naturality ((forget F).mapDerivedCategoryFactorsh.hom.app K)]
    erw [reassoc_of% (hα K)]
    rw [← hcp]
    simp only [Category.assoc, Functor.comp_obj, Iso.hom_inv_id_app, Category.comp_id]
    rfl
  intro M N hM hN hJM hJN
  have hqM := DerivedCategory.TStructure.t.bounded.prop_of_iso (a.app M).symm hJM
  have hqN := DerivedCategory.TStructure.t.bounded.prop_of_iso (a.app N).symm hJN
  have hfq := hf M N hM hN hqM hqN
  have ht (r : ℤ) (v : CyclicDerivedHom F M N r) : cyclicDerivedHomTransport F G
      (P.rightDerivedFunctorOfQuasiIsoResolutions hP)
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
      (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
      (cyclicDerivedRightForgetComparison F G L e hP hC) M N r v =
    V.map (a.hom.app M) ≫
      cyclicDerivedHomTransport F G P.rightDerivedFunctor L.rightDerivedFunctor
        (fun r ↦ L.rightDerivedFunctor.commShiftIso r) α M N r v ≫
      (V.map (a.inv.app N))⟦r⟧' := by
    rw [← hβ]
    exact model_transport U V _ _ _ _ a c α M N r v
  have ht' (r : ℤ) (v : CyclicDerivedHom F M N r) :
      cyclicDerivedHomTransport F G P.rightDerivedFunctor L.rightDerivedFunctor
        (fun r ↦ L.rightDerivedFunctor.commShiftIso r) α M N r v =
    V.map (a.inv.app M) ≫ cyclicDerivedHomTransport F G
      (P.rightDerivedFunctorOfQuasiIsoResolutions hP)
      (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
      (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
      (cyclicDerivedRightForgetComparison F G L e hP hC) M N r v ≫
        (V.map (a.hom.app N))⟦r⟧' := by
    rw [ht]
    simp only [Category.assoc, ← V.map_comp_assoc, Iso.inv_hom_id_app,
      V.map_id, Category.id_comp]
    rw [← Functor.map_comp, ← V.map_comp, Iso.inv_hom_id_app, V.map_id,
      Functor.map_id, Category.comp_id]
  refine ⟨transport_additive F G _ _ _ _ M N, ?_, transport_forget F G _ _ _, ?_⟩
  · intro r v
    rw [ht', hfq.2.1 r v]
    have he := action_change_endpoints G (a.app M).symm (a.app N).symm r
      (cyclicDerivedHomTransport F G (P.rightDerivedFunctorOfQuasiIsoResolutions hP)
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
        (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
        (cyclicDerivedRightForgetComparison F G L e hP hC) M N r v)
    change V.map (a.inv.app M) ≫ _ ≫ (V.map (a.hom.app N))⟦r⟧' =
      cyclicDerivedHomAction G _ _ r
        (V.map (a.inv.app M) ≫ _ ≫ (V.map (a.hom.app N))⟦r⟧') at he
    rw [← ht' r v] at he
    exact he
  · intro v
    have hnat := hn' _ _ _ _ hqM hqN hJM hJN (a.inv.app M) (a.hom.app N)
      (cyclicDerivedHomTransport F G (P.rightDerivedFunctorOfQuasiIsoResolutions hP)
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
        (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
        (cyclicDerivedRightForgetComparison F G L e hP hC) M N (-1) v)
    have ha_map : P.rightDerivedFunctor.map (b M N hM hN (QuotientAddGroup.mk v)) =
        a.inv.app M ≫ (P.rightDerivedFunctorOfQuasiIsoResolutions hP).map
          (b M N hM hN (QuotientAddGroup.mk v)) ≫ a.hom.app N := by
      rw [a.hom.naturality]
      simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    rw [ha_map, hfq.2.2.2 v, hnat]
    congr 2
    change V.map (a.inv.app M) ≫
      cyclicDerivedHomTransport F G (P.rightDerivedFunctorOfQuasiIsoResolutions hP)
        (L.rightDerivedFunctorOfQuasiIsoResolutions hC)
        (fun r ↦ (L.rightDerivedFunctorOfQuasiIsoResolutions hC).commShiftIso r)
        (cyclicDerivedRightForgetComparison F G L e hP hC) M N (-1) v ≫
        (V.map (a.hom.app N))⟦(-1 : ℤ)⟧' = _
    rw [ht]
    simp only [Category.assoc, ← V.map_comp_assoc, Iso.inv_hom_id_app,
      V.map_id, Category.id_comp]
    rw [← Functor.map_comp, ← V.map_comp, Iso.inv_hom_id_app, V.map_id,
      Functor.map_id, Category.comp_id]

end CategoryTheory.Endofunctor.IsoAlgebra
