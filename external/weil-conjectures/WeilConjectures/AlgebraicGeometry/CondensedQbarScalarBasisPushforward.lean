/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! Explicit central scalar actions and their derived direct-image compatibility.

Source: the scalar-action and adjunction calculations of
`WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/Compatibility.lean`.
The shared unitor and center-transport lemmas are moved here under their original names;
the source module imports this API, so neither consumer duplicates those proofs.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂
open CategoryTheory Limits MonoidalCategory MonObj Abelian
open scoped CategoryTheory.Obj CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- The regular-module left unitor composes with the tensor quotient to give the action.
Source: Colimit/Compatibility.lean, the original `tensorπ_leftUnitor_hom` proof.
(auxiliary; not a blueprint node) -/
lemma tensorπ_leftUnitor_hom (M : Mod C S) :
    tensorObjπ (regular S) M ≫ (λ_ M).hom.hom = γ[S,M.X] := by
  change coequalizer.π _ _ ≫
    ((_root_.Bimod.whiskerRight (toBimodRegularIso (R := S)).hom
        ((toBimod S).obj M)).hom ≫
      _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M)) = _
  rw [← Category.assoc]
  dsimp only [_root_.Bimod.whiskerRight]
  change (colimit.ι _ WalkingParallelPair.one ≫ colimMap _) ≫ _ = _
  rw [ι_colimMap]
  simp only [parallelPairHom_app_one, toBimodRegularIso_hom_hom, id_whiskerRight]
  change (𝟙 (S ⊗ M.X) ≫ coequalizer.π _ _) ≫
    _root_.Bimod.LeftUnitorBimod.hom ((toBimod S).obj M) = _
  rw [Category.id_comp]
  dsimp only [_root_.Bimod.LeftUnitorBimod.hom]
  exact coequalizer.π_desc _ _

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
/-- The underlying inverse left unitor inserts the coefficient unit before the tensor quotient.
Source: Colimit/Compatibility.lean, the original `leftUnitor_inv_hom` proof.
(auxiliary; not a blueprint node) -/
lemma leftUnitor_inv_hom (M : Mod C S) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ η[S] ▷ M.X ≫ tensorObjπ (regular S) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [← comp_hom', Iso.inv_hom_id, id_hom']
  simp only [Category.assoc]
  rw [tensorπ_leftUnitor_hom, one_act, Iso.inv_hom_id]

@[no_expose] noncomputable def qbar_scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) : M ⟶ M :=
  (λ_ M).inv ≫ (regularLift (regular S) b ▷ M) ≫ (λ_ M).hom

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma qbar_scalarEndo_hom (b : 𝟙_ C ⟶ S) (M : Mod C S) :
    (qbar_scalarEndo b M).hom = (λ_ M.X).inv ≫ b ▷ M.X ≫ γ[S,M.X] := by
  simp only [qbar_scalarEndo, comp_hom', leftUnitor_inv_hom, Category.assoc]
  rw [tensorObjπ_whiskerRight_assoc, tensorπ_leftUnitor_hom]
  rw [← comp_whiskerRight_assoc, one_comp_regularLift]

@[no_expose] noncomputable def qbar_scalarNatEndo (b : 𝟙_ C ⟶ S) :
    CatCenter (Mod C S) where
  asHom :=
    { app M := qbar_scalarEndo b M
      naturality M N f := by
        apply hom_ext
        simp only [CategoryTheory.Functor.id_map, comp_hom', qbar_scalarEndo_hom]
        rw [leftUnitor_inv_naturality_assoc f.hom, whisker_exchange_assoc, ← act_hom]
        simp only [Category.assoc] }

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
lemma qbar_scalarNatEndo_app (b : 𝟙_ C ⟶ S) (M : Mod C S) :
    (qbar_scalarNatEndo b).app M = qbar_scalarEndo b M := (rfl)

end CategoryTheory.Mod

namespace CategoryTheory
variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
@[no_expose] noncomputable def qbar_complexCenter (τ : CatCenter A) :
    CatCenter (CochainComplex A ℤ) where
  asHom :=
    { app K :=
        { f i := τ.app (K.X i)
          comm' i j _ := by simpa using (τ.naturality (K.d i j)).symm }
      naturality K L f := by
        ext i
        exact τ.naturality (f.f i) }

omit [HasDerivedCategory A] in
lemma qbar_complexCenter_app_f (τ : CatCenter A) (K : CochainComplex A ℤ) (i : ℤ) :
    ((qbar_complexCenter τ).app K).f i = τ.app (K.X i) := (rfl)

@[no_expose] noncomputable def qbar_homotopyCenter (τ : CatCenter A) :
    CatCenter (HomotopyCategory A (.up ℤ)) where
  asHom :=
    { app K := (HomotopyCategory.quotient A (.up ℤ)).map ((qbar_complexCenter τ).app K.as)
      naturality K L f := by
        let f' : K.as ⟶ L.as := (HomotopyCategory.quotient A (.up ℤ)).preimage f
        have hf : (HomotopyCategory.quotient A (.up ℤ)).map f' = f :=
          (HomotopyCategory.quotient A (.up ℤ)).map_preimage f
        simp only [CategoryTheory.Functor.id_map]
        rw [← hf, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg (HomotopyCategory.quotient A (.up ℤ)).map
          ((qbar_complexCenter τ).naturality f') }

omit [HasDerivedCategory A] in
lemma qbar_homotopyCenter_app (τ : CatCenter A) (K : HomotopyCategory A (.up ℤ)) :
    (qbar_homotopyCenter τ).app K =
      (HomotopyCategory.quotient A (.up ℤ)).map ((qbar_complexCenter τ).app K.as) := (rfl)

@[no_expose] noncomputable def qbar_derivedCenter (τ : CatCenter A) :
    CatCenter (DerivedCategory A) :=
  (qbar_homotopyCenter τ).localization DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (.up ℤ))

lemma qbar_derivedCenter_Qh (τ : CatCenter A) (K : HomotopyCategory A (.up ℤ)) :
    (qbar_derivedCenter τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((qbar_homotopyCenter τ).app K) :=
  CatCenter.localization_app _ _ _ _
end CategoryTheory

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- One scalar leg of the derived extension-unit copower. Its computation is given by
`qbar_scalarUnitLeg_eq`; keeping the construction folded avoids repeatedly expanding derived
functor data while indexing concrete coefficient-basis statements. -/
@[no_expose] noncomputable def qbar_scalarUnitLeg (b : 𝟙_ C ⟶ S)
    (M : DerivedCategory (Mod C R)) :
    M ⟶ (comap φ).mapDerivedCategory.obj ((extendScalars φ).leftDerivedFunctor.obj M) :=
  (derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
    (comap φ).mapDerivedCategory.map
      ((qbar_derivedCenter (qbar_scalarNatEndo b)).app ((extendScalars φ).leftDerivedFunctor.obj M))

lemma qbar_scalarUnitLeg_eq (b : 𝟙_ C ⟶ S) (M : DerivedCategory (Mod C R)) :
    qbar_scalarUnitLeg φ b M =
      (derivedExtendMapDerivedCategoryAdjunction φ).unit.app M ≫
        (comap φ).mapDerivedCategory.map
          ((qbar_derivedCenter (qbar_scalarNatEndo b)).app
            ((extendScalars φ).leftDerivedFunctor.obj M)) := (rfl)
end CategoryTheory.Mod

namespace CategoryTheory
section Central
variable {A B : Type*} [Category A] [Category B]
  (F : A ⥤ B) {G : B ⥤ A} (adj : F ⊣ G)
  (τA : CatCenter A) (τB : CatCenter B)
include adj in
/-- A right adjoint preserves central actions whenever its left adjoint does.
Source: Colimit/Compatibility.lean, the original `map_center_rightAdjoint` proof.
(auxiliary; not a blueprint node) -/
lemma map_center_rightAdjoint
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (Y : B) :
    G.map (τB.app Y) = τA.app (G.obj Y) := by
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, hF]
  rw [adj.counit_naturality]
  exact τB.naturality (adj.counit.app Y)

end Central
end CategoryTheory

namespace CategoryTheory.Mod
section MapScalar
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v₁} C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [MonoidalCategory D]
  [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
  [IsGrothendieckAbelian.{v₂} D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Monoidal] {S : C} [MonObj S] [IsCommMonObj S]
  [IsCommMonObj (F.obj S)]
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C]
  [MonoidalPreadditive D] [Abelian.HasFunctorialFlatResolution D] in
private lemma qbar_map_scalarEndo (b : 𝟙_ C ⟶ S) (M : Mod C S) :
    (F.mapMod S).map (qbar_scalarEndo b M) =
      qbar_scalarEndo (Functor.LaxMonoidal.ε F ≫ F.map b) ((F.mapMod S).obj M) := by
  apply hom_ext
  change F.map (qbar_scalarEndo b M).hom = _
  rw [qbar_scalarEndo_hom, qbar_scalarEndo_hom]
  simp only [CategoryTheory.Functor.map_comp, comp_whiskerRight, Category.assoc]
  change F.map (λ_ M.X).inv ≫ F.map (b ▷ M.X) ≫ F.map γ[S,M.X] =
    (λ_ (F.obj M.X)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj M.X ≫
      F.map b ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F S M.X ≫ F.map γ[S,M.X]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  have hunit : F.map (λ_ M.X).inv =
      (λ_ (F.obj M.X)).inv ≫ Functor.LaxMonoidal.ε F ▷ F.obj M.X ≫
        Functor.LaxMonoidal.μ F (𝟙_ C) M.X := by
    apply (cancel_mono (F.map (λ_ M.X).hom)).1
    simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    rw [← Functor.LaxMonoidal.left_unitality F M.X]
    exact (Iso.inv_hom_id _).symm
  rw [hunit]
  simp only [Category.assoc]
end MapScalar
end CategoryTheory.Mod

namespace CategoryTheory
variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (τA : CatCenter A) (τB : CatCenter B)
private lemma qbar_map_derivedCenter
    (hF : ∀ X, F.map (τA.app X) = τB.app (F.obj X)) (M : DerivedCategory A) :
    F.mapDerivedCategory.map ((qbar_derivedCenter τA).app M) =
      (qbar_derivedCenter τB).app (F.mapDerivedCategory.obj M) := by
  have h : CategoryTheory.Functor.whiskerRight (qbar_derivedCenter τA).asHom
      F.mapDerivedCategory =
      CategoryTheory.Functor.whiskerLeft F.mapDerivedCategory (qbar_derivedCenter τB).asHom := by
    apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ))
    intro K
    dsimp only [CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app]
    apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K)).1
    simp only [qbar_derivedCenter_Qh]
    have h₁ := F.mapDerivedCategoryFactorsh.hom.naturality ((qbar_homotopyCenter τA).app K)
    have h₂ := (qbar_derivedCenter τB).naturality (F.mapDerivedCategoryFactorsh.hom.app K)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at h₁ h₂
    rw [qbar_derivedCenter_Qh] at h₂
    rw [← h₂, h₁]
    apply congrArg (F.mapDerivedCategoryFactorsh.hom.app K ≫ ·)
    apply congrArg DerivedCategory.Qh.map
    change (F.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient _ (.up ℤ)).map ((qbar_complexCenter τA).app K.as)) = _
    rw [CategoryTheory.Functor.mapHomotopyCategory_map]
    apply congrArg (HomotopyCategory.quotient _ (.up ℤ)).map
    ext n
    exact hF (K.as.X n)
  exact NatTrans.congr_app h M
end CategoryTheory

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma qbar_comap_scalarEndo (b : 𝟙_ C ⟶ R) (N : Mod C S) :
    (comap φ).map (qbar_scalarEndo (b ≫ φ) N) = qbar_scalarEndo b ((comap φ).obj N) := by
  apply hom_ext
  change (qbar_scalarEndo (b ≫ φ) N).hom = (qbar_scalarEndo b ((comap φ).obj N)).hom
  simp only [qbar_scalarEndo_hom, comp_whiskerRight, Category.assoc]
  rfl

omit [MonoidalPreadditive C] [Abelian.HasFunctorialFlatResolution C] in
private lemma qbar_extendIso_scalarEndo [IsIso φ] (b : 𝟙_ C ⟶ R) (M : Mod C R) :
    (extendScalars φ).map (qbar_scalarEndo b M) =
      qbar_scalarEndo (b ≫ φ) ((extendScalars φ).obj M) := by
  let e := extendScalarsIsoComapInv φ
  apply (cancel_mono (e.hom.app M)).1
  rw [e.hom.naturality]
  have h := (qbar_scalarNatEndo (b ≫ φ)).naturality (e.hom.app M)
  dsimp only [CategoryTheory.Functor.id_map, qbar_scalarNatEndo] at h
  rw [← h]
  congr 1
  have hb : b ≫ φ ≫ inv φ = b := by simp
  change (comap (inv φ)).map (qbar_scalarEndo b M) = _
  simpa only [asIso_inv, Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    (qbar_comap_scalarEndo (inv φ) (b ≫ φ) M)
end CategoryTheory.Mod

namespace CategoryTheory
section CenterTransport
variable {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
/-- Transport preservation of central actions across a natural isomorphism of functors.
Source: Colimit/Compatibility.lean, the original `map_center_of_iso` proof.
(auxiliary; not a blueprint node) -/
lemma map_center_of_iso (e : F ≅ G) (τA : CatCenter A) (τB : CatCenter B)
    (hG : ∀ X, G.map (τA.app X) = τB.app (G.obj X)) (X : A) :
    F.map (τA.app X) = τB.app (F.obj X) := by
  apply (cancel_mono (e.hom.app X)).1
  rw [e.hom.naturality, hG]
  exact τB.naturality _
end CenterTransport
end CategoryTheory

namespace AlgebraicGeometry.ProEtale
open Scheme
namespace CondensedRing
open Abelian MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false

section ScalarCompatibility
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
private lemma qbar_upperStar_scalarEndo
    (b : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    (f)^*⟦Λ⟧.map (Mod.qbar_scalarEndo b M) =
      Mod.qbar_scalarEndo
        (CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map b ≫ condensedPullbackHom Λ f) ((f)^*⟦Λ⟧.obj M) := by
  change (Mod.extendScalars (condensedPullbackHom Λ f)).map
    ((((f)^*[Ab.{u + 1}]).mapMod _).map (Mod.qbar_scalarEndo b M)) = _
  rw [Mod.qbar_map_scalarEndo, Mod.qbar_extendIso_scalarEndo]
  simp only [Category.assoc]
  rfl
private lemma qbar_lowerStar_derivedScalarEndo
    (b : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    R((f)_*⟦Λ⟧).map
        ((CategoryTheory.qbar_derivedCenter (Mod.qbar_scalarNatEndo
          (CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
            (f)^*[Ab.{u + 1}].map b ≫ condensedPullbackHom Λ f))).app M) =
      (CategoryTheory.qbar_derivedCenter (Mod.qbar_scalarNatEndo b)).app (R((f)_*⟦Λ⟧).obj M) := by
  apply CategoryTheory.map_center_rightAdjoint L((f)^*⟦Λ⟧)
    (derivedUpperStarLowerStarAdjunction Λ f)
  intro N
  apply CategoryTheory.map_center_of_iso
    (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory
  apply CategoryTheory.qbar_map_derivedCenter
  intro K
  exact qbar_upperStar_scalarEndo f b K
lemma qbar_lowerStar_derivedScalarEndo_of_eq
    (bX : 𝟙_ (Sheaf (ProEt.topology X) Ab.{u + 1}) ⟶ condensedRingObj Λ X)
    (bY : 𝟙_ (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ condensedRingObj Λ Y)
    (hb : bX = CategoryTheory.Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
      (f)^*[Ab.{u + 1}].map bY ≫ condensedPullbackHom Λ f)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    R((f)_*⟦Λ⟧).map ((CategoryTheory.qbar_derivedCenter (Mod.qbar_scalarNatEndo bX)).app M) =
      (CategoryTheory.qbar_derivedCenter (Mod.qbar_scalarNatEndo bY)).app (R((f)_*⟦Λ⟧).obj M) := by
  rw [hb]
  exact qbar_lowerStar_derivedScalarEndo f bY M
end ScalarCompatibility

end CondensedRing
end AlgebraicGeometry.ProEtale

-- Keep the explicit scalar constructions folded in the coordinate-existence statement.
attribute [irreducible] CategoryTheory.qbar_derivedCenter
  CategoryTheory.qbar_homotopyCenter CategoryTheory.qbar_complexCenter
  CategoryTheory.Mod.qbar_scalarNatEndo CategoryTheory.Mod.qbar_scalarEndo
