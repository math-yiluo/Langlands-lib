/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniverses
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # A tensor precomposition map invertible over a pulled-back open

Source: Stacks Project, Tags 08DW, 08DX and 0E4G, Lemma 48.4.4.
(blueprint: lem-sc-derived-tensor-precomposition-open).
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory Limits

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry


/-- Homology is unchanged by the unique comparison of localizations. -/
private noncomputable def homologyComparison (X : Scheme.{u})
    (h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (n : ℤ) :
    (@schemeDerivedStandardEquivalence X h).functor ⋙
        @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n ≅
      @DerivedCategory.homologyFunctor _ _ _ h n := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let hs := HasDerivedCategory.standard A
  let E := @schemeDerivedStandardEquivalence X h
  let q : @DerivedCategory.Q A _ _ h ⋙ E.functor ≅
      @DerivedCategory.Q A _ _ hs :=
    (Functor.isoWhiskerRight (@DerivedCategory.quotientCompQhIso A _ _ h)
      E.functor).symm ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.quotient A (.up ℤ))
      (Localization.compUniqFunctor (@DerivedCategory.Qh A _ _ h)
        (@DerivedCategory.Qh A _ _ hs) (HomotopyCategory.quasiIso A (.up ℤ))) ≪≫
    @DerivedCategory.quotientCompQhIso A _ _ hs
  let H := @DerivedCategory.homologyFunctor A _ _ hs n
  let α := (Functor.associator (@DerivedCategory.Q A _ _ h) _ H).symm ≪≫
    Functor.isoWhiskerRight q H ≪≫ @DerivedCategory.homologyFunctorFactors A _ _ hs n
  let β := @DerivedCategory.homologyFunctorFactors A _ _ h n
  exact (Localization.fullyFaithfulWhiskeringLeft (@DerivedCategory.Q A _ _ h)
    (HomologicalComplex.quasiIso A (.up ℤ)) A).preimageIso (α ≪≫ β.symm)

/-- The unit is the same degree-zero structure module in both localizations. -/
private noncomputable def unitComparison (X : Scheme.{u})
    (h : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    (@schemeDerivedStandardEquivalence X h).functor.obj
      (𝟙_ (@schemeDerivedCategory X h)) ≅
      𝟙_ (@schemeDerivedCategory X (HasDerivedCategory.standard _)) := by
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  exact (Localization.compUniqFunctor (@DerivedCategory.Qh A _ _ h)
    (@DerivedCategory.Qh A _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso A (.up ℤ))).app
      ((HomotopyCategory.singleFunctor A 0).obj (SheafOfModules.unit X.ringCatSheaf))

private theorem pullbackQCoh {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : schemeDerivedCategory Y) (hI : schemeDerivedQCohProperty Y I) :
    schemeDerivedQCohProperty X ((derivedPullbackAcrossUniverses f).obj I) := by
  let eY := @schemeDerivedStandardEquivalence Y hy
  let eX := @schemeDerivedStandardEquivalence X hx
  have hIs : @schemeDerivedQCohProperty Y (HasDerivedCategory.standard _)
      (eY.functor.obj I) := by
    intro n
    exact (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).prop_of_iso
      ((homologyComparison Y hy n).app I).symm (hI n)
  have hL := (@derivedPullback_tensor_preserve_QCoh X Y f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)).1 _ hIs
  intro n
  let J := (@derivedPullback X Y f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _)).obj (eY.functor.obj I)
  let c := ((homologyComparison X hx n).app (eX.inverse.obj J)).symm ≪≫
    (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).mapIso
      (eX.counitIso.app J)
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    c.symm (hL n)

private theorem pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    Nonempty ((derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
      𝟙_ (schemeDerivedCategory X)) := by
  let eY := @schemeDerivedStandardEquivalence Y hy
  let eX := @schemeDerivedStandardEquivalence X hx
  let L := @derivedPullback X Y f (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _)
  obtain ⟨m, _⟩ := @exists_derivedPullbackMonoidalModel X Y f
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
  exact ⟨eX.inverse.mapIso (L.mapIso (unitComparison Y hy) ≪≫ m.εIso.symm) ≪≫
    eX.inverse.mapIso (unitComparison X hx).symm ≪≫
    (eX.unitIso.app (𝟙_ (schemeDerivedCategory X))).symm⟩

/-- An exact functor commutes with equivalences of localizations. -/
private theorem exact_transport
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hA₁ : HasDerivedCategory.{wX} A) (hB₁ : HasDerivedCategory.{wY} B)
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

/-- Deriving the composite of two exact functors agrees with their derived composite. -/
private theorem exactCompIso
    {A B C : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [Category* C] [Abelian C]
    (hA : HasDerivedCategory.{wX} A) (hB : HasDerivedCategory.{wY} B)
    (hC : HasDerivedCategory.{u} C) (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Nonempty (@Functor.mapDerivedCategory _ _ _ hA _ _ _ hC (F ⋙ G) _ _ _ ≅
      @Functor.mapDerivedCategory _ _ _ hA _ _ _ hB F _ _ _ ⋙
        @Functor.mapDerivedCategory _ _ _ hB _ _ _ hC G _ _ _) :=
  ⟨(@Functor.mapDerivedCategoryCompIso A _ _ hA B _ _ hB C _ _ hC
    F _ _ _ G _ _ _).symm⟩

/-- Exact derived composition preserves an isomorphism already inverted by the first map. -/
private theorem exactComp_preservesIso
    {A B C : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [Category* C] [Abelian C]
    (hA : HasDerivedCategory.{wX} A) (hB : HasDerivedCategory.{wY} B)
    (hC : HasDerivedCategory.{u} C) (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {M N : @DerivedCategory A _ _ hA} (a : M ⟶ N)
    (ha : IsIso ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hB F _ _ _).map a)) :
    IsIso ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hC (F ⋙ G) _ _ _).map a) := by
  obtain ⟨c⟩ := exactCompIso hA hB hC F G
  exact (NatIso.isIso_map_iff c a).mpr (by
    change IsIso ((@Functor.mapDerivedCategory _ _ _ hB _ _ _ hC G _ _ _).map
      ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hB F _ _ _).map a))
    have := ha
    infer_instance)

/-- An exact equivalence as the second factor reflects derived invertibility. -/
private theorem exactComp_reflectsIso
    {A B C : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [Category* C] [Abelian C]
    (hA : HasDerivedCategory.{wX} A) (hB : HasDerivedCategory.{wY} B)
    (hC : HasDerivedCategory.{u} C) (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.IsEquivalence]
    {M N : @DerivedCategory A _ _ hA} (a : M ⟶ N)
    (ha : IsIso ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hC (F ⋙ G) _ _ _).map a)) :
    IsIso ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hB F _ _ _).map a) := by
  obtain ⟨c⟩ := exactCompIso hA hB hC F G
  have : IsIso ((@Functor.mapDerivedCategory _ _ _ hB _ _ _ hC G _ _ _).map
      ((@Functor.mapDerivedCategory _ _ _ hA _ _ _ hB F _ _ _).map a)) :=
    (NatIso.isIso_map_iff c a).mp ha
  exact isIso_of_reflects_iso _
    (@Functor.mapDerivedCategory _ _ _ hB _ _ _ hC G _ _ _)

/-- Reflection through an equivalence, without unfolding its localization construction. -/
private theorem reflectEquivalenceIso
    {C D : Type*} [Category* C] [Category* D] (e : C ≌ D)
    {M N : C} (a : M ⟶ N) (ha : IsIso (e.functor.map a)) : IsIso a := by
  have := ha
  exact isIso_of_reflects_iso a e.functor

/-- Pullback preserves arrows which become invertible on the given open. -/
private theorem pullbackLocalIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hy : HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens)
    (hOX : HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (f ⁻¹ᵁ V))))
    (hOY : HasDerivedCategory.{wY}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)))
    {I J : @schemeDerivedCategory Y hy} (a : I ⟶ J)
    (ha : IsIso ((@Functor.mapDerivedCategory _ _ _ hy _ _ _ hOY
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V) _ _ _).map a)) :
    IsIso ((@Functor.mapDerivedCategory _ _ _ hx _ _ _ hOX
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (f ⁻¹ᵁ V)) _ _ _).map
        ((@derivedPullbackAcrossUniverses X Y f hx hy).map a)) := by
  let U := f ⁻¹ᵁ V
  let AX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let AY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let BX := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let BY := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)
  -- Reuse these structures throughout the localization comparisons.
  let : Abelian AX := inferInstance
  let : Abelian AY := inferInstance
  let : Abelian BX := inferInstance
  let : Abelian BY := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := inferInstance
  let : Abelian (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) := inferInstance
  let RX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let RY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V
  let hBX : HasDerivedCategory.{wX} BX := hOX
  let hBY : HasDerivedCategory.{wY} BY := hOY
  let sX := HasDerivedCategory.standard AX
  let sY := HasDerivedCategory.standard AY
  let sBX := HasDerivedCategory.standard BX
  let sBY := HasDerivedCategory.standard BY
  let sU := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let sV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let eX := @schemeDerivedStandardEquivalence X hx
  let eY := @schemeDerivedStandardEquivalence Y hy
  let eBX := Localization.uniq (@DerivedCategory.Qh BX _ _ hBX)
    (@DerivedCategory.Qh BX _ _ sBX) (HomotopyCategory.quasiIso BX (.up ℤ))
  let eBY := Localization.uniq (@DerivedCategory.Qh BY _ _ hBY)
    (@DerivedCategory.Qh BY _ _ sBY) (HomotopyCategory.quasiIso BY (.up ℤ))
  let RXd := @Functor.mapDerivedCategory _ _ _ hx _ _ _ hBX RX _ _ _
  let RYd := @Functor.mapDerivedCategory _ _ _ hy _ _ _ hBY RY _ _ _
  let RXs := @Functor.mapDerivedCategory _ _ _ sX _ _ _ sBX RX _ _ _
  let RYs := @Functor.mapDerivedCategory _ _ _ sY _ _ _ sBY RY _ _ _
  let eU : BX ≌ SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv U
  let eV : BY ≌ SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv V
  let EU : BX ⥤ SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := eU.functor
  let EV : BY ⥤ SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := eV.functor
  have : EU.Additive := Functor.additive_of_preserves_binary_products _
  have : EV.Additive := Functor.additive_of_preserves_binary_products _
  let RUs := @Functor.mapDerivedCategory _ _ _ sX _ _ _ sU (RX ⋙ EU) _ _ _
  let RVs := @Functor.mapDerivedCategory _ _ _ sY _ _ _ sV (RY ⋙ EV) _ _ _
  let L := @derivedPullback X Y f sY sX
  obtain ⟨αX⟩ := @exact_transport AX BX
    (inferInstance : Category AX) (inferInstance : Abelian AX)
    (inferInstance : Category BX) (inferInstance : Abelian BX)
    RX inferInstance inferInstance inferInstance hx hBX sX sBX
  obtain ⟨αY⟩ := @exact_transport AY BY
    (inferInstance : Category AY) (inferInstance : Abelian AY)
    (inferInstance : Category BY) (inferInstance : Abelian BY)
    RY inferInstance inferInstance inferInstance hy hBY sY sBY
  have hYs : IsIso (RYs.map (eY.functor.map a)) := by
    have : IsIso ((RYd ⋙ eBY.functor).map a) := by
      have : IsIso (RYd.map a) := ha
      change IsIso (eBY.functor.map (RYd.map a))
      infer_instance
    exact (NatIso.isIso_map_iff αY a).mp inferInstance
  have : IsIso (RVs.map (eY.functor.map a)) :=
    exactComp_preservesIso sY sBY sV RY EV _ hYs
  obtain ⟨γ⟩ := @derivedPullback_openRestriction_iso X Y f U V le_rfl sX sY sU sV
  let LO := @derivedPullback U.toScheme V.toScheme (f.resLE V U le_rfl) sV sU
  have : IsIso (RUs.map (L.map (eY.functor.map a))) :=
    (NatIso.isIso_map_iff γ (eY.functor.map a)).mpr (by
      change IsIso (LO.map (RVs.map (eY.functor.map a)))
      infer_instance)
  have : IsIso (RXs.map (L.map (eY.functor.map a))) :=
    exactComp_reflectsIso sX sBX sU RX EU _ inferInstance
  let δ : (eX.inverse ⋙ eX.functor) ⋙ RXs ≅ RXs :=
    Functor.isoWhiskerRight eX.counitIso RXs ≪≫ Functor.leftUnitor RXs
  have hMapped :
      IsIso (RXs.map (eX.functor.map (eX.inverse.map (L.map (eY.functor.map a))))) :=
    (NatIso.isIso_map_iff δ (L.map (eY.functor.map a))).mpr inferInstance
  have : IsIso (eBX.functor.map (RXd.map ((@derivedPullbackAcrossUniverses X Y f hx hy).map a))) :=
    (NatIso.isIso_map_iff αX
      ((@derivedPullbackAcrossUniverses X Y f hx hy).map a)).mpr hMapped
  exact reflectEquivalenceIso eBX _ inferInstance



/-- Transport a chosen localization along an exact equivalence of abelian categories.
This is the localization construction in `SchemeIsoDerivedLocalizations`, specialized
to the module-sheaf universe; its helper there is private. -/
private theorem hasDerivedCategory_of_equivalence {C D : Type (u + 1)}
    [Category.{u} C] [Category.{u} D] [Abelian C] [Abelian D]
    (e : C ≌ D) [HasDerivedCategory.{wX} D] : Nonempty (HasDerivedCategory.{wX} C) := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let eC := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := eC.functor ⋙ (DerivedCategory.Q (C := D))
  have : L.IsLocalization (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
    refine Functor.IsLocalization.of_equivalence_source
      (DerivedCategory.Q (C := D)) (HomologicalComplex.quasiIso D (ComplexShape.up ℤ))
      L (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) eC.symm ?_ ?_ ?_
    · intro K M f hf
      have : QuasiIso f := hf
      exact (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).le_isoClosure _
        (show QuasiIso (eC.inverse.map f) from
          (show QuasiIso ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
            from inferInstance))
    · intro K M f hf
      have : QuasiIso f := hf
      have : QuasiIso (eC.functor.map f) :=
        (show QuasiIso ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          from inferInstance)
      exact inferInstanceAs (IsIso (DerivedCategory.Q.map (eC.functor.map f)))
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  exact ⟨{ D := DerivedCategory D, L := L }⟩

/-- Exact restriction sends a locally invertible tensor arrow to an isomorphism. -/
private theorem tensorLocalIso (X : Scheme.{u}) (U : X.Opens)
    [hx : HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [ho : HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    {A B : schemeDerivedCategory X} (a : A ⟶ B) (P : schemeDerivedCategory X)
    (ha : IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map a)) :
    IsIso ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.map (a ▷ P)) := by
  let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv U
  let E : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := e.functor
  obtain ⟨hD⟩ := hasDerivedCategory_of_equivalence e.symm
  let : HasDerivedCategory.{wX}
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := hD
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let RD := @Functor.mapDerivedCategory _ _ _ hx _ _ _ hD (R ⋙ E) _ _ _
  let Ed := @Functor.mapDerivedCategory _ _ _ ho _ _ _ hD E _ _ _
  let R0 := @Functor.mapDerivedCategory _ _ _ hx _ _ _ ho R _ _ _
  let c : RD ≅ R0 ⋙ Ed :=
    (@Functor.mapDerivedCategoryCompIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ hx
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _ _ ho
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ hD
      R _ _ _ E _ _ _).symm
  have : IsIso (RD.map a) :=
    (NatIso.isIso_map_iff c a).mpr (by
      have : IsIso (R0.map a) := ha
      change IsIso (Ed.map (R0.map a))
      infer_instance)
  obtain ⟨γ⟩ := @derivedTensor_openRestriction_iso X U hx hD
  let : MonoidalCategory (@schemeDerivedCategory U.toScheme hD) :=
    @schemeDerivedTensorMonoidal U.toScheme hD
  let δ : tensorRight P ⋙ RD ≅ RD ⋙ tensorRight (RD.obj P) :=
    NatIso.ofComponents (fun K ↦ (γ.app K).app P) (by
      intro K L b
      exact congrArg (fun t ↦ t.app P) (γ.hom.naturality b))
  have : IsIso (RD.map (a ▷ P)) :=
    (NatIso.isIso_map_iff δ a).mpr (by
      change IsIso (RD.map a ▷ RD.obj P)
      infer_instance)
  have : IsIso (Ed.map (R0.map (a ▷ P))) :=
    (NatIso.isIso_map_iff c (a ▷ P)).mp inferInstance
  exact isIso_of_reflects_iso _ Ed

/-- Pull back a perfect map to the tensor unit and tensor it with P.
Source: Stacks Project, Tags 08DW(1), 08DX(1), and Tag 0E4G, Lemma 48.4.4,
last paragraph.
(blueprint: lem-sc-derived-tensor-precomposition-open).

Proof: Work first in the standard derived localizations. The tensor unit is the
structure sheaf in degree zero, and its pullback is the tensor unit on X; the
K-flat pullback of the structure sheaf gives this isomorphism e. Perfect I has
quasi-coherent cohomology. Pullback preserves quasi-coherent cohomology by 08DW,
and tensor preserves it by 08DX, giving the assertion about Lf*I tensor P.
Restriction to U = f inverse image V commutes with derived pullback and derived
tensor. Thus restriction of Lf*i is pullback of i restricted to V, and is invertible.
Its tensor with P restricted to U is invertible, as are the restrictions of e
and the left unitor. Their composite is therefore invertible. Transport the
pullback and these identifications through the unique localization equivalences
in derivedPullbackAcrossUniverses to the specified independent universes and
through exact restriction to the specified open categories. Naturality of those
comparisons identifies the transported composite with the displayed map.
No adjunction, direct image, annihilation hypothesis or support of P is used.
For empty V, zero P or I equal to the unit the same isomorphism computations apply.
The existential e is not used to define chosen data. -/
theorem exists_derivedTensor_precomposition_open
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i)) :
    ∃ e : (derivedPullbackAcrossUniverses f).obj (𝟙_ (schemeDerivedCategory Y)) ≅
        𝟙_ (schemeDerivedCategory X),
      schemeDerivedQCohProperty X ((derivedPullbackAcrossUniverses f).obj I ⊗ P.obj) ∧
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map
          ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
            e.hom ▷ P.obj ≫ (λ_ P.obj).hom)) := by
  let hx : HasDerivedCategory.{wX}
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let hy : HasDerivedCategory.{wY}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) := inferInstance
  let hOX : ∀ W : X.Opens, HasDerivedCategory.{wX}
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) := inferInstance
  let hOY : ∀ W : Y.Opens, HasDerivedCategory.{wY}
    (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W)) := inferInstance
  obtain ⟨e⟩ := @pullbackUnit X Y f hx hy
  refine ⟨e, canonical_derivedTensor_preserve_QCoh X _ _
    (pullbackQCoh f I (schemeDerivedQCohProperty_of_isPerfect Y I hI)) P.property, ?_⟩
  have hLi := @pullbackLocalIso X Y f hx hy V (hOX (f ⁻¹ᵁ V)) (hOY V) _ _ i hi
  have hTensor := @tensorLocalIso X (f ⁻¹ᵁ V) hx (hOX (f ⁻¹ᵁ V)) _ _
    ((derivedPullbackAcrossUniverses f).map i) P.obj hLi
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

end AlgebraicGeometry
