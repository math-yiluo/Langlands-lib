/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Derived pullback restriction with independent localization universes

Source: Stacks Project, Tag 08DW, compatibility with restriction to opens.
(blueprint: lem-pc-derived-pullback-open-restriction-universes).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Transport a right Kan extension across equivalences of its domain and codomain. -/
private theorem kanExtension_transport
    {C D₁ D₂ H₁ H₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    [Category* H₁] [Category* H₂]
    (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂) (S : D₁ ≌ D₂) (T : H₁ ≌ H₂)
    (e : L₁ ⋙ S.functor ≅ L₂)
    (F₁ : C ⥤ H₁) (F₂ : C ⥤ H₂) (t : F₁ ⋙ T.functor ≅ F₂)
    (G₁ : D₁ ⥤ H₁) (G₂ : D₂ ⥤ H₂)
    (α₁ : L₁ ⋙ G₁ ⟶ F₁) (α₂ : L₂ ⋙ G₂ ⟶ F₂)
    [G₁.IsRightKanExtension α₁] [G₂.IsRightKanExtension α₂] :
    Nonempty (G₁ ⋙ T.functor ≅ S.functor ⋙ G₂) := by
  let β := (Functor.associator L₁ G₁ T.functor).inv ≫
    Functor.whiskerRight α₁ T.functor
  have : (Functor.RightExtension.postcompose₂ L₁ F₁ T.functor).IsEquivalence := by
    dsimp only [Functor.RightExtension.postcompose₂]
    have : IsIso (show
        ((Functor.whiskeringRight D₁ H₁ H₂).obj T.functor) ⋙
          (Functor.whiskeringLeft C D₁ H₂).obj L₁ ⟶
        (Functor.whiskeringLeft C D₁ H₁).obj L₁ ⋙
          (Functor.whiskeringRight C H₁ H₂).obj T.functor from
        { app G := (Functor.associator L₁ G T.functor).inv }) :=
      NatIso.isIso_of_isIso_app _
    apply CostructuredArrow.isEquivalenceMap₂
  have hβ : (G₁ ⋙ T.functor).IsRightKanExtension β := by
    exact ⟨⟨IsTerminal.equivOfIso
      (Functor.RightExtension.postcompose₂ObjMkIso T.functor α₁)
      (IsTerminal.isTerminalObj
        (Functor.RightExtension.postcompose₂ L₁ F₁ T.functor) _
        (Functor.isUniversalOfIsRightKanExtension G₁ α₁))⟩⟩
  let γ := (Functor.associator L₁ S.functor G₂).inv ≫
    Functor.whiskerRight e.hom G₂ ≫ α₂
  have : (S.functor ⋙ G₂).IsRightKanExtension γ :=
    (Functor.isRightKanExtension_iff_postcomp₁ S.functor e α₂).mp inferInstance
  exact ⟨Functor.rightKanExtensionUniqueOfIso (G₁ ⋙ T.functor) β t
    (S.functor ⋙ G₂) γ⟩

/-- The chosen derived pullbacks commute with equivalences of localizations. -/
private theorem pullback_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hY₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (hX₂ : HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hY₂ : HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) :
    Nonempty
      (@derivedPullback _ _ f hY₁ hX₁ ⋙
        (Localization.uniq (@DerivedCategory.Qh _ _ _ hX₁)
          (@DerivedCategory.Qh _ _ _ hX₂) (HomotopyCategory.quasiIso _ (.up ℤ))).functor ≅
      (Localization.uniq (@DerivedCategory.Qh _ _ _ hY₁)
        (@DerivedCategory.Qh _ _ _ hY₂) (HomotopyCategory.quasiIso _ (.up ℤ))).functor ⋙
          @derivedPullback _ _ f hY₂ hX₂) := by
  obtain ⟨I₁, hi₁, him₁, hia₁, hil₁, hic₁, hir₁, E₁, he₁, hem₁, hea₁,
    ε₁, hε₁, ht₁, hf₁⟩ := @derivedPullback_spec _ _ f hY₁ hX₁
  obtain ⟨I₂, hi₂, him₂, hia₂, hil₂, hic₂, hir₂, E₂, he₂, hem₂, hea₂,
    ε₂, hε₂, ht₂, hf₂⟩ := @derivedPullback_spec _ _ f hY₂ hX₂
  let η : E₁ ≅ E₂ := NatIso.ofComponents
    (fun M ↦ eqToIso ((he₁ M).trans (he₂ M).symm)) (by
      intro M N a
      dsimp
      rw [hem₁, hem₂]
      simp)
  let qX₁ := @DerivedCategory.Qh _ _ _ hX₁
  let qX₂ := @DerivedCategory.Qh _ _ _ hX₂
  let qY₁ := @DerivedCategory.Qh _ _ _ hY₁
  let qY₂ := @DerivedCategory.Qh _ _ _ hY₂
  let WX := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let WY := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  let S := Localization.uniq qY₁ qY₂ WY
  let T := Localization.uniq qX₁ qX₂ WX
  let e := Localization.compUniqFunctor qY₁ qY₂ WY
  let ηh : E₁.mapHomotopyCategory (.up ℤ) ≅ E₂.mapHomotopyCategory (.up ℤ) :=
    { hom := η.hom.mapHomotopyCategory (.up ℤ)
      inv := η.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  let t : (E₁.mapHomotopyCategory (.up ℤ) ⋙ qX₁) ⋙ T.functor ≅
      E₂.mapHomotopyCategory (.up ℤ) ⋙ qX₂ :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Localization.compUniqFunctor qX₁ qX₂ WX) ≪≫
      Functor.isoWhiskerRight ηh qX₂
  have : (@derivedPullback _ _ f hY₁ hX₁).IsRightKanExtension ε₁ :=
    hε₁.isRightKanExtension
  have : (@derivedPullback _ _ f hY₂ hX₂).IsRightKanExtension ε₂ :=
    hε₂.isRightKanExtension
  exact kanExtension_transport qY₁ qY₂ S T e _ _ t _ _ ε₁ ε₂

/-- An exact functor commutes with equivalences of localizations. -/
private theorem exact_transport
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hA₁ : HasDerivedCategory.{w} A) (hB₁ : HasDerivedCategory.{wO} B)
    (hA₂ : HasDerivedCategory.{u} A) (hB₂ : HasDerivedCategory.{u} B) :
    Nonempty
      (@Functor.mapDerivedCategory _ _ _ hA₁ _ _ _ hB₁ F _ _ _ ⋙
        (Localization.uniq (@DerivedCategory.Qh _ _ _ hB₁)
          (@DerivedCategory.Qh _ _ _ hB₂) (HomotopyCategory.quasiIso B (.up ℤ))).functor ≅
      (Localization.uniq (@DerivedCategory.Qh _ _ _ hA₁)
        (@DerivedCategory.Qh _ _ _ hA₂) (HomotopyCategory.quasiIso A (.up ℤ))).functor ⋙
          @Functor.mapDerivedCategory _ _ _ hA₂ _ _ _ hB₂ F _ _ _) := by
  let qA₁ := @DerivedCategory.Qh _ _ _ hA₁
  let qA₂ := @DerivedCategory.Qh _ _ _ hA₂
  let qB₁ := @DerivedCategory.Qh _ _ _ hB₁
  let qB₂ := @DerivedCategory.Qh _ _ _ hB₂
  let WA := HomotopyCategory.quasiIso A (.up ℤ)
  let WB := HomotopyCategory.quasiIso B (.up ℤ)
  let eA := (Localization.uniq qA₁ qA₂ WA).functor
  let eB := (Localization.uniq qB₁ qB₂ WB).functor
  let F₁ := @Functor.mapDerivedCategory _ _ _ hA₁ _ _ _ hB₁ F _ _ _
  let F₂ := @Functor.mapDerivedCategory _ _ _ hA₂ _ _ _ hB₂ F _ _ _
  let α : qA₁ ⋙ (F₁ ⋙ eB) ≅ F.mapHomotopyCategory (.up ℤ) ⋙ qB₂ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactorsh _ _ _ hA₁ _ _ _ hB₁ F _ _ _) eB ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Localization.compUniqFunctor qB₁ qB₂ WB)
  let β : qA₁ ⋙ (eA ⋙ F₂) ≅ F.mapHomotopyCategory (.up ℤ) ⋙ qB₂ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Localization.compUniqFunctor qA₁ qA₂ WA) F₂ ≪≫
      @Functor.mapDerivedCategoryFactorsh _ _ _ hA₂ _ _ _ hB₂ F _ _ _
  exact ⟨((Functor.whiskeringLeft _ _ _).obj qA₁).preimageIso (α ≪≫ β.symm)⟩

/-- Restriction comparison with a possibly different localization universe on opens.
Source: Stacks Project, Tag 08DW, proof of compatibility with restriction.
Proof: choose K-flat resolutions on Y. Restriction preserves quasi-isomorphisms and
K-flatness, and termwise tensor pullback commutes with restriction. The two composites
are thus naturally identified on K-flat resolutions and descend through localization.
Alternatively transport the existing same-universe comparison along the canonical
equivalences between choices of localization; its naturality makes the transported
comparison independent of the representatives. The comparison has no quasi-coherence
or affineness hypothesis and works for the empty open and arbitrary unbounded objects.
(blueprint: lem-pc-derived-pullback-open-restriction-universes). -/
theorem derivedPullback_openRestriction_iso_universes {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty (derivedPullback f ⋙
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙
        derivedPullback (f.resLE V U hUV)) := by
  let AX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let AY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let AU := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let AV := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)
  let hX : HasDerivedCategory.{w} AX := inferInstance
  let hY : HasDerivedCategory.{w} AY := inferInstance
  let hU : HasDerivedCategory.{wO} AU := inferInstance
  let hV : HasDerivedCategory.{wO} AV := inferInstance
  let sX := HasDerivedCategory.standard AX
  let sY := HasDerivedCategory.standard AY
  let sU := HasDerivedCategory.standard AU
  let sV := HasDerivedCategory.standard AV
  let RX : AX ⥤ AU :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := AU) (Scheme.Modules.overEquiv U)
  let RY : AY ⥤ AV :=
    SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
        (D := AV) (Scheme.Modules.overEquiv V)
  let eY := (Localization.uniq (@DerivedCategory.Qh _ _ _ hY)
    (@DerivedCategory.Qh _ _ _ sY) (HomotopyCategory.quasiIso AY (.up ℤ))).functor
  let eU := (Localization.uniq (@DerivedCategory.Qh _ _ _ hU)
    (@DerivedCategory.Qh _ _ _ sU) (HomotopyCategory.quasiIso AU (.up ℤ))).functor
  let L := @derivedPullback _ _ f hY hX
  let LO := @derivedPullback _ _ (f.resLE V U hUV) hV hU
  let LOs := @derivedPullback _ _ (f.resLE V U hUV) sV sU
  let RXd := @Functor.mapDerivedCategory _ _ _ hX _ _ _ hU RX _ _ _
  let RYd := @Functor.mapDerivedCategory _ _ _ hY _ _ _ hV RY _ _ _
  let RXs := @Functor.mapDerivedCategory _ _ _ sX _ _ _ sU RX _ _ _
  obtain ⟨αX⟩ := exact_transport RX hX hU sX sU
  obtain ⟨αY⟩ := exact_transport RY hY hV sY sV
  obtain ⟨β⟩ := pullback_transport f hX hY sX sY
  obtain ⟨βO⟩ := pullback_transport (f.resLE V U hUV) hU hV sU sV
  obtain ⟨γ⟩ := @derivedPullback_openRestriction_iso _ _ f U V hUV sX sY sU sV
  let δ : (L ⋙ RXd) ⋙ eU ≅ (RYd ⋙ LO) ⋙ eU :=
    Functor.isoWhiskerLeft L αX ≪≫
      Functor.isoWhiskerRight β RXs ≪≫
      Functor.isoWhiskerLeft eY γ ≪≫
      Functor.isoWhiskerRight αY.symm LOs ≪≫
      Functor.isoWhiskerLeft RYd βO.symm
  exact ⟨((Functor.whiskeringRight _ _ _).obj eU).preimageIso δ⟩

end AlgebraicGeometry
