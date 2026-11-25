/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import WeilConjectures.AlgebraicGeometry.DivisibleExtensionDerivedReduction
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
import WeilConjectures.SixFunctors.BaseChange.DerivedForget

/-!
# The quotient-normalized derived residue unit

The scalar unit is identified with the actual quotient morphism, and its universal
property is tested against every unbounded complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ w₄ wAb wMod
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} E]
variable (F : C ⥤ D) (G : D ⥤ E)
  [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
private theorem singleComparison (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) := by
  dsimp [mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
  simp only [Functor.map_id, Category.id_comp, Category.comp_id]
private theorem derivedCompSingle (X : C) :
    (mapDerivedCategoryCompIso F G).inv.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) =
      ((F ⋙ G).mapDerivedCategorySingleFunctor 0).hom.app X := by
  rw [← cancel_epi ((mapDerivedCategoryCompIso F G).hom.app _),
    Iso.hom_inv_id_app_assoc]
  exact (F.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app
    G X 0).symm
variable (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] in
private theorem cochainNatSingle (e : F ≅ H) (X : C) :
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).hom.app X =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
      (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X) := by
  ext i
  by_cases h : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
    exact (e.hom.naturality_assoc _ _).symm
  · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne, h]

private theorem derivedNatSingle (e : F ≅ H) (X : C) :
    (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app X =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  rw [singleComparison F, singleComparison H]
  erw [mapDerivedCategoryNatIso_fac_assoc]
  have hs : (DerivedCategory.singleFunctor D 0).map (e.hom.app X) =
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X)) := rfl
  rw [hs]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun z ↦ F.mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single C (.up ℤ) 0).obj X) ≫ DerivedCategory.Q.map z)
      (cochainNatSingle F H e X)

private theorem derivedTripleNatSingle
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w₄} B]
    (K : E ⥤ B) [K.Additive] [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (M : C ⥤ B) [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    (e : F ⋙ G ⋙ K ≅ M) (X : C) :
    let ρ := Functor.isoWhiskerLeft F.mapDerivedCategory
        (Functor.mapDerivedCategoryCompIso G K) ≪≫
      (Functor.mapDerivedCategoryCompIso F (G ⋙ K)) ≪≫
        Functor.mapDerivedCategoryNatIso e
    ρ.hom.app ((DerivedCategory.singleFunctor C 0).obj X) ≫
        (M.mapDerivedCategorySingleFunctor 0).hom.app X =
      K.mapDerivedCategory.map
          (G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
            (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X)) ≫
        (K.mapDerivedCategorySingleFunctor 0).hom.app (G.obj (F.obj X)) ≫
          (DerivedCategory.singleFunctor B 0).map (e.hom.app X) := by
  dsimp only
  change ((Functor.mapDerivedCategoryCompIso G K).hom.app _ ≫
      (Functor.mapDerivedCategoryCompIso F (G ⋙ K)).hom.app _ ≫
        (Functor.mapDerivedCategoryNatIso e).hom.app _) ≫ _ = _
  simp only [Category.assoc]
  rw [derivedNatSingle (F ⋙ G ⋙ K) M e X]
  rw [← derivedCompSingle F (G ⋙ K) X]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [← (Functor.mapDerivedCategoryCompIso G K).hom.naturality_assoc]
  rw [← derivedCompSingle G K (F.obj X)]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf.ConstantResidue
variable {C : Type (u + 1)} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasSheafify J CommRingCat.{u + 1}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
variable [HasSheafify J AddCommGrpCat.{u + 1}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

private abbrev coefficientRing (A : Type (u + 1)) [CommRing A] :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A))

private def coefficientMap (A : Type (u + 1)) [CommRing A] :
    (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ (coefficientRing J A).obj :=
  Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private instance (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallyInjective J (coefficientMap J A) := by
  apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
  change Presheaf.IsLocallyInjective J (Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) (forget CommRingCat.{u + 1}))
  infer_instance

private instance (A : Type (u + 1)) [CommRing A] :
    Presheaf.IsLocallySurjective J (coefficientMap J A) := by
  apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
  change Presheaf.IsLocallySurjective J (Functor.whiskerRight (toSheafify J
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))) (forget CommRingCat.{u + 1}))
  infer_instance

private def realize (A : Type (u + 1)) [CommRing A] :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ SheafOfModules.{u + 1} (coefficientRing J A) :=
  sheafToPresheaf J (ModuleCat.{u + 1} A) ⋙
    AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf C A ⋙
    PresheafOfModules.sheafification (coefficientMap J A)

private instance (A : Type (u + 1)) [CommRing A] : (realize J A).IsEquivalence :=
  AlgebraicGeometry.ProEtale.coefficientRealization_isEquivalence J A
    (coefficientRing J A) (coefficientMap J A)

private def realizeForgetIso (A : Type (u + 1)) [CommRing A] :
    realize J A ⋙ SheafOfModules.toSheaf.{u + 1} (coefficientRing J A) ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents (fun F ↦ asIso ((sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.app
    ((sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj F)))
    (fun f ↦ (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit.naturality
      ((sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map f))

private abbrev forgetSheaf (A : Type (u + 1)) [CommRing A] :
    Sheaf J (ModuleCat.{u + 1} A) ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  sheafCompose J (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})

set_option backward.isDefEq.respectTransparency false in
private def forgetSheafFullyFaithful (A : Type (u + 1)) [CommRing A]
    [(forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).Full] :
    (forgetSheaf J A).FullyFaithful where
  preimage f := ObjectProperty.homMk
    { app U := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).preimage (f.hom.app U)
      naturality U V i := by
        apply (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map_injective
        rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage,
          Functor.map_preimage]
        exact f.hom.naturality i }
  map_preimage f := by
    ext U : 3
    exact (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map_preimage _
  preimage_map f := by
    ext U : 3
    exact (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).preimage_map _

private instance : (forgetSheaf J (ULift.{u + 1} ℤ)).IsEquivalence := by
  let F := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).Full :=
    (forgetSheafFullyFaithful J _).full
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).Faithful :=
    (forgetSheafFullyFaithful J _).faithful
  have : (forgetSheaf J (ULift.{u + 1} ℤ)).EssSurj := by
    constructor
    intro G
    let ε := F.asEquivalence.counitIso
    refine ⟨(sheafCompose J F.inv).obj G, ⟨?_⟩⟩
    exact
      { hom := (sheafCompose_map J ε.hom).app G
        inv := (sheafCompose_map J ε.inv).app G
        hom_inv_id := by
          rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.hom_inv_id]
          rfl
        inv_hom_id := by
          rw [← NatTrans.comp_app, ← sheafCompose_comp, ε.inv_hom_id]
          rfl }
  exact Functor.IsEquivalence.mk

private instance integerForget_isEquivalence :
    (SheafOfModules.toSheaf.{u + 1} (coefficientRing J (ULift.{u + 1} ℤ))).IsEquivalence := by
  have : (realize J (ULift.{u + 1} ℤ) ⋙
      SheafOfModules.toSheaf.{u + 1} (coefficientRing J (ULift.{u + 1} ℤ))).IsEquivalence :=
    Functor.isEquivalence_of_iso (realizeForgetIso J (ULift.{u + 1} ℤ)).symm
  exact Functor.isEquivalence_of_comp_left (realize J (ULift.{u + 1} ℤ)) _

private theorem universal_transport
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    (U : A ⥤ B) (U' : A' ⥤ B') (E : A' ⥤ A) (T : B ⥤ B')
    [E.Full] [E.Faithful] [T.Full] [T.Faithful]
    (ρ : E ⋙ U ⋙ T ≅ U') {F : B} {F' : B'} {H : A} {H' : A'}
    (eF : T.obj F ≅ F') (eH : E.obj H' ≅ H) (p : F ⟶ U.obj H)
    (hp : ∀ K : A, Function.Bijective (fun f : H ⟶ K ↦ p ≫ U.map f)) :
    ∀ K : A', Function.Bijective (fun f : H' ⟶ K ↦
      (eF.inv ≫ T.map (p ≫ U.map eH.inv) ≫ ρ.hom.app H') ≫ U'.map f) := by
  intro K
  have h := (((Functor.FullyFaithful.ofFullyFaithful T).homEquiv).bijective.comp
    (hp (E.obj K))).comp
    (eH.homFromEquiv.bijective.comp (Functor.FullyFaithful.ofFullyFaithful E).homEquiv.bijective)
  have h' := ((ρ.app K).homToEquiv.bijective.comp
    (eF.homFromEquiv.bijective.comp h))
  convert h' using 1
  ext f
  simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.homToEquiv_apply,
    Functor.FullyFaithful.homEquiv_apply]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom]
  rw [← ρ.hom.naturality f]
  rfl

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance (A : Type (u + 1)) [CommRing A] : (realize J A).Additive :=
  Functor.additive_of_preserves_binary_products _

private theorem universal_single_transport
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    [HasDerivedCategory.{w₃} A'] [HasDerivedCategory.{w₄} B']
    (E : A' ⥤ A) (U : A ⥤ B) (TZ : B ⥤ B') (V : A' ⥤ B')
    [E.IsEquivalence] [TZ.IsEquivalence]
    [E.Additive] [U.Additive] [TZ.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (ρ₀ : E ⋙ U ⋙ TZ ≅ V) (X : B) (H : A') (F : B') (c : TZ.obj X ≅ F)
    (p0 : X ⟶ U.obj (E.obj H)) (p1 : F ⟶ V.obj H)
    (hp0 : TZ.map p0 = c.hom ≫ p1 ≫ (ρ₀.inv.app H))
    (hunit : ∀ K : DerivedCategory A,
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj (E.obj H) ⟶ K ↦
        (DerivedCategory.singleFunctor _ 0).map p0 ≫
          (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H) ≫
            U.mapDerivedCategory.map f)) :
    ∀ K : DerivedCategory A',
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj H ⟶ K ↦
        (DerivedCategory.singleFunctor _ 0).map p1 ≫
          (V.mapDerivedCategorySingleFunctor 0).inv.app H ≫ V.mapDerivedCategory.map f) := by
  let ρ : E.mapDerivedCategory ⋙ U.mapDerivedCategory ⋙ TZ.mapDerivedCategory ≅
      V.mapDerivedCategory :=
    Functor.isoWhiskerLeft E.mapDerivedCategory (Functor.mapDerivedCategoryCompIso U TZ) ≪≫
      (Functor.mapDerivedCategoryCompIso E (U ⋙ TZ)) ≪≫
        Functor.mapDerivedCategoryNatIso ρ₀
  let sZ := DerivedCategory.singleFunctor B 0
  let sR := DerivedCategory.singleFunctor A 0
  let eF : TZ.mapDerivedCategory.obj (sZ.obj X) ≅
      (DerivedCategory.singleFunctor B' 0).obj F :=
    (TZ.mapDerivedCategorySingleFunctor 0).app X ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso c
  let eH : E.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj H) ≅ sR.obj (E.obj H) :=
    (E.mapDerivedCategorySingleFunctor 0).app H
  have htransport := universal_transport U.mapDerivedCategory V.mapDerivedCategory
    E.mapDerivedCategory TZ.mapDerivedCategory ρ eF eH
    (sZ.map p0 ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H))
    (fun K ↦ by simpa only [Category.assoc] using hunit K)
  have hρ := Functor.derivedTripleNatSingle E U TZ V ρ₀ H
  let sA := DerivedCategory.singleFunctor B' 0
  change ρ.hom.app ((DerivedCategory.singleFunctor _ 0).obj H) ≫
      (V.mapDerivedCategorySingleFunctor 0).hom.app H =
    TZ.mapDerivedCategory.map
        (U.mapDerivedCategory.map eH.hom ≫
          (U.mapDerivedCategorySingleFunctor 0).hom.app (E.obj H)) ≫
      (TZ.mapDerivedCategorySingleFunctor 0).hom.app (U.obj (E.obj H)) ≫ sA.map (ρ₀.hom.app H) at hρ
  have hcan : ((sZ.map p0 ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H)) ≫
      U.mapDerivedCategory.map eH.inv) ≫
        (U.mapDerivedCategory.map eH.hom ≫
          (U.mapDerivedCategorySingleFunctor 0).hom.app (E.obj H)) = sZ.map p0 := by
    simp only [Category.assoc, ← U.mapDerivedCategory.map_comp_assoc,
      Iso.inv_hom_id, U.mapDerivedCategory.map_id, Category.id_comp,
      Iso.inv_hom_id_app]
    exact Category.comp_id (sZ.map p0)
  simp only [Category.assoc] at hcan
  have hnorm : eF.inv ≫ TZ.mapDerivedCategory.map
      ((sZ.map p0 ≫ (U.mapDerivedCategorySingleFunctor 0).inv.app (E.obj H)) ≫
        U.mapDerivedCategory.map eH.inv) ≫
        ρ.hom.app ((DerivedCategory.singleFunctor _ 0).obj H) =
      sA.map p1 ≫ (V.mapDerivedCategorySingleFunctor 0).inv.app H := by
    apply (Iso.eq_comp_inv ((V.mapDerivedCategorySingleFunctor 0).app H)).2
    simp only [Category.assoc, Iso.app_hom]
    erw [hρ]
    erw [← TZ.mapDerivedCategory.map_comp_assoc]
    simp only [Category.assoc]
    erw [hcan]
    erw [(TZ.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc p0]
    dsimp only [eF, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    change sA.map c.inv ≫ sA.map (TZ.map p0) ≫ sA.map (ρ₀.hom.app H) = sA.map p1
    rw [hp0]
    simp only [← Functor.map_comp]
    congr 1
    simp
  intro K
  have hfinal := htransport K
  rw [hnorm] at hfinal
  simpa only [Category.assoc] using hfinal

attribute [local irreducible] realize

open SheafOfModules.DivisibleReduction in
private theorem ringed_quotient_unit [EssentiallySmall.{u + 1} C] [HasTerminal C]
    (n : ℕ) (hn : 0 < n) (Fc : Integral J) (Q : Residue J n)
    (pc : Fc ⟶ (restriction J n).obj Q) (wpc : (n • 𝟙 Fc) ≫ pc = 0)
    (hquot : (ShortComplex.mk (n • 𝟙 Fc) pc wpc).ShortExact) :
    ∀ K : DerivedCategory (Residue J n),
      Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj Q ⟶ K ↦
        (DerivedCategory.singleFunctor _ 0).map pc ≫
          ((restriction J n).mapDerivedCategorySingleFunctor 0).inv.app Q ≫
            (derivedRestriction n).map f) := by
  let S : ShortComplex (Integral J) := ShortComplex.mk (0 : (0 : Integral J) ⟶ Fc) (𝟙 Fc) (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_mono rfl).2 (by dsimp [S]; infer_instance)
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; infer_instance }
  let i : (restriction J n).obj (0 : Residue J n) ⟶ S.X₁ := 0
  have wi : i ≫ (n • 𝟙 S.X₁) = 0 := by simp [i]
  have hi : Mono i :=
    ((restriction J n).map_isZero (isZero_zero _)).mono i
  have hepi : Epi (n • 𝟙 S.X₁) :=
    (isZero_zero (Integral J)).epi _
  have hgmono : Mono (n • 𝟙 S.X₁) := (isZero_zero (Integral J)).mono _
  have hk : (ShortComplex.mk i (n • 𝟙 S.X₁) wi).ShortExact :=
    { exact := (ShortComplex.exact_iff_mono _ rfl).2 hgmono
      mono_f := hi
      epi_g := hepi }
  let P : Presentation (J := J) n :=
    { S := S
      exact := hS
      H := (0 : Residue J n)
      Q := Q
      i := i
      p := pc
      wi := wi
      wp := wpc
      kummer := hk
      quotient := hquot }
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (projection J n)
  let I := identifications n D hn P
  let ad := SheafOfModules.sheafScalarDerivedAdjunction (projection J n) D
  let sZ := DerivedCategory.singleFunctor (Integral J) 0
  let sR := DerivedCategory.singleFunctor (Residue J n) 0
  have heq : eta n D Fc ≫ (derivedRestriction n).map I.alphaF.hom =
      sZ.map pc ≫ ((restriction J n).mapDerivedCategorySingleFunctor 0).inv.app Q := by
    apply (Iso.eq_comp_inv (((restriction J n).mapDerivedCategorySingleFunctor 0).app Q)).2
    simpa only [Category.assoc, Iso.app_hom] using I.quotient_unit
  intro K
  have h := (ad.homEquiv (sZ.obj Fc) K).bijective.comp
    I.alphaF.symm.homFromEquiv.bijective
  convert h using 1
  ext f
  simp only [Function.comp_apply, Iso.homFromEquiv_apply,
    Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ (derivedRestriction n).map f) heq.symm

open SheafOfModules.DivisibleReduction in
/-- On an essentially small site with a terminal object, sheafification and the usual abelian sheaf
exactness assumptions, let n>0, G an abelian sheaf, H a sheaf of ULift(Z/n)-modules and U the
coefficient-forgetting functor. If n:G→G followed by p:G→UH is short exact, then p satisfies
DerivedUnit [def-sp-exact-functor-derived-unit], in any chosen unbounded derived categories.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (auxiliary; not a blueprint node).
Proof: Realize raw module sheaves as modules over the constant residue ring and abelian sheaves as
integer modules. Apply normalized divisible-extension reduction to the split presentation 0→G→G. Its
quotient identification identifies the adjunction unit with p. Transport the Hom bijections along
the integer-module and raw-module equivalences. Exact-functor single comparisons identify the
transported map with single(p). The argument is valid for n=1 and zero sheaves. -/
theorem quotient_derived_unit [EssentiallySmall.{u + 1} C] [HasTerminal C]
    (n : ℕ) (hn : 0 < n)
    (F : Sheaf J AddCommGrpCat.{u + 1})
    (H : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    [HasDerivedCategory.{wAb} (Sheaf J AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{wMod}
      (Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))]
    [(sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).Additive]
    [PreservesFiniteLimits (sheafCompose J
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}))]
    [PreservesFiniteColimits (sheafCompose J
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1}))]
    (p : F ⟶ (sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).obj H)
    (hp : (n • 𝟙 F) ≫ p = 0)
    (hP : (ShortComplex.mk (n • 𝟙 F) p hp).ShortExact) :
    (sheafCompose J (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
      AddCommGrpCat.{u + 1})).DerivedUnit F H p := by
  unfold Functor.DerivedUnit
  let R := ULift.{u + 1} (ZMod n)
  let TZ : Integral J ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
    SheafOfModules.toSheaf.{u + 1} (coefficientRing J (ULift.{u + 1} ℤ))
  have : TZ.IsEquivalence := integerForget_isEquivalence J
  have : PreservesFiniteLimits TZ := inferInstance
  have : PreservesFiniteColimits TZ := inferInstance
  let Fc : Integral J := TZ.asEquivalence.inverse.obj F
  let c : TZ.obj Fc ≅ F := TZ.asEquivalence.counitIso.app F
  let Q : Residue J n := (realize J R).obj H
  let d : TZ.obj ((restriction J n).obj Q) ≅ (forgetSheaf J R).obj H :=
    (realizeForgetIso J R).app H
  let pc : Fc ⟶ (restriction J n).obj Q := TZ.preimage (c.hom ≫ p ≫ d.inv)
  have hpc : TZ.map pc = c.hom ≫ p ≫ d.inv := TZ.map_preimage _
  have wpc : (n • 𝟙 Fc) ≫ pc = 0 := by
    apply TZ.map_injective
    rw [TZ.map_comp, TZ.map_nsmul, TZ.map_id, hpc, TZ.map_zero]
    calc
      (n • 𝟙 (TZ.obj Fc)) ≫ (c.hom ≫ p ≫ d.inv) =
          c.hom ≫ ((n • 𝟙 F) ≫ p) ≫ d.inv := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp]
      _ = 0 := by rw [hp, zero_comp, comp_zero]
  let SQ : ShortComplex (Integral J) := ShortComplex.mk (n • 𝟙 Fc) pc wpc
  let SA : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}) :=
    ShortComplex.mk (n • 𝟙 F) p hp
  have eQ : SQ.map TZ ≅ SA := by
    refine ShortComplex.isoMk c c d ?_ ?_
    · change c.hom ≫ (n • 𝟙 F) = TZ.map (n • 𝟙 Fc) ≫ c.hom
      simp only [TZ.map_nsmul, TZ.map_id, Preadditive.nsmul_comp,
        Preadditive.comp_nsmul, Category.comp_id, Category.id_comp]
    · change c.hom ≫ p = TZ.map pc ≫ d.hom
      rw [hpc]
      simp
  have hquot : SQ.ShortExact :=
    (CategoryTheory.ShortExact.shortExact_map_iff TZ).1
      (ShortComplex.shortExact_of_iso eQ.symm hP)
  have hunit := ringed_quotient_unit J n hn Fc Q pc wpc hquot
  let sZ := DerivedCategory.singleFunctor (Integral J) 0
  let sR := DerivedCategory.singleFunctor (Residue J n) 0
  exact universal_single_transport (realize J R) (restriction J n) TZ (forgetSheaf J R)
    (realizeForgetIso J R) Fc H F c pc p hpc hunit

end CategoryTheory.Sheaf.ConstantResidue
