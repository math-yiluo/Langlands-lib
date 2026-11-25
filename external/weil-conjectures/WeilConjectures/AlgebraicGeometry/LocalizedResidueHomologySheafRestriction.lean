/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Open restriction comparison before residue global sections

Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-sc-localized-residue-homology-sheaf-restriction).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace AlgebraicGeometry


set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
    exact ⟨⟨Limits.IsTerminal.equivOfIso
      (Functor.RightExtension.postcompose₂ObjMkIso T.functor α₁)
      (Limits.IsTerminal.isTerminalObj
        (Functor.RightExtension.postcompose₂ L₁ F₁ T.functor) _
        (Functor.isUniversalOfIsRightKanExtension G₁ α₁))⟩⟩
  let γ := (Functor.associator L₁ S.functor G₂).inv ≫
    Functor.whiskerRight e.hom G₂ ≫ α₂
  have : (S.functor ⋙ G₂).IsRightKanExtension γ :=
    (Functor.isRightKanExtension_iff_postcomp₁ S.functor e α₂).mp inferInstance
  exact ⟨Functor.rightKanExtensionUniqueOfIso (G₁ ⋙ T.functor) β t
    (S.functor ⋙ G₂) γ⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chosen derived pullbacks commute with equivalences of localizations. -/
private theorem pullback_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hY₁ : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    (hX₂ : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
    (hY₂ : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) :
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

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Change only the localization on the source of an exact derived functor. -/
private theorem exact_source_transport
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (hA₁ : HasDerivedCategory.{w} A) (hA₂ : HasDerivedCategory.{u + 1} A)
    (hB : HasDerivedCategory.{u + 1} B) :
    Nonempty
      (@Functor.mapDerivedCategory _ _ _ hA₁ _ _ _ hB F _ _ _ ≅
      (Localization.uniq (@DerivedCategory.Qh _ _ _ hA₁)
        (@DerivedCategory.Qh _ _ _ hA₂) (HomotopyCategory.quasiIso A (.up ℤ))).functor ⋙
          @Functor.mapDerivedCategory _ _ _ hA₂ _ _ _ hB F _ _ _) := by
  let q₁ := @DerivedCategory.Qh _ _ _ hA₁
  let q₂ := @DerivedCategory.Qh _ _ _ hA₂
  let e := (Localization.uniq q₁ q₂ (HomotopyCategory.quasiIso A (.up ℤ))).functor
  let F₁ := @Functor.mapDerivedCategory _ _ _ hA₁ _ _ _ hB F _ _ _
  let F₂ := @Functor.mapDerivedCategory _ _ _ hA₂ _ _ _ hB F _ _ _
  let α : q₁ ⋙ (e ⋙ F₂) ≅ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Localization.compUniqFunctor q₁ q₂ (HomotopyCategory.quasiIso A (.up ℤ))) F₂ ≪≫
      @Functor.mapDerivedCategoryFactorsh _ _ _ hA₂ _ _ _ hB F _ _ _
  exact ⟨((Functor.whiskeringLeft _ _ _).obj q₁).preimageIso
    (@Functor.mapDerivedCategoryFactorsh _ _ _ hA₁ _ _ _ hB F _ _ _ ≪≫ α.symm)⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Homology is independent of the chosen localization. -/
private theorem homology_transport
    (A : Type*) [Category* A] [Abelian A]
    (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{u + 1} A) (n : ℤ) :
    Nonempty
      ((Localization.uniq (@DerivedCategory.Qh _ _ _ h₁)
        (@DerivedCategory.Qh _ _ _ h₂) (HomotopyCategory.quasiIso A (.up ℤ))).functor ⋙
          @DerivedCategory.homologyFunctor _ _ _ h₂ n ≅
        @DerivedCategory.homologyFunctor _ _ _ h₁ n) := by
  let q₁ := @DerivedCategory.Qh _ _ _ h₁
  let q₂ := @DerivedCategory.Qh _ _ _ h₂
  let α := (Functor.associator q₁ _ _).symm ≪≫
    Functor.isoWhiskerRight
        (Localization.compUniqFunctor q₁ q₂ (HomotopyCategory.quasiIso A (.up ℤ)))
      (@DerivedCategory.homologyFunctor _ _ _ h₂ n) ≪≫
    @DerivedCategory.homologyFunctorFactorsh _ _ _ h₂ n ≪≫
    (@DerivedCategory.homologyFunctorFactorsh _ _ _ h₁ n).symm
  exact ⟨((Functor.whiskeringLeft _ _ _).obj q₁).preimageIso α⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An exact tensor pullback computes its own left derived functor. -/
private theorem exact_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hY : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive]
    [Limits.PreservesFiniteLimits (Scheme.Modules.tensorPullback f)]
    [Limits.PreservesFiniteColimits (Scheme.Modules.tensorPullback f)] :
    Nonempty (derivedPullback f ≅
      @Functor.mapDerivedCategory _ _ _ hY _ _ _ hX
        (Scheme.Modules.tensorPullback f) _ _ _) := by
  obtain ⟨_, _, _, _, _, _, _, F, hF, hFm, _, ε, hL, _, _⟩ :=
    derivedPullback_spec f
  have h : F = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFm a)
  subst F
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback f
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback f).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact ⟨Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback f) ε
    T.mapDerivedCategoryFactorsh.hom W⟩

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor pullback along a scheme isomorphism is an equivalence. -/
private theorem tensorPullback_iso_equivalence {Y Y' : Scheme.{u}} (i : Y' ≅ Y) :
    (Scheme.Modules.tensorPullback i.hom).IsEquivalence := by
  obtain ⟨c₁⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.inv i.hom
  obtain ⟨c₂⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.hom i.inv
  obtain ⟨u₁⟩ := Scheme.Modules.nonempty_tensorPullbackId Y
  obtain ⟨u₂⟩ := Scheme.Modules.nonempty_tensorPullbackId Y'
  let a := c₁.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback i.inv_hom_id) ≪≫ u₁
  let b := c₂.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback i.hom_inv_id) ≪≫ u₂
  exact (CategoryTheory.Equivalence.mk (Scheme.Modules.tensorPullback i.hom)
    (Scheme.Modules.tensorPullback i.inv) a.symm b).isEquivalence_functor

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The residue homology sheaf of a restriction is the tensor pullback of the original
residue homology sheaf, before applying global sections or changing their scalars.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-sc-localized-residue-homology-sheaf-restriction).

Proof: exact over-site restriction followed by overEquiv is tensor pullback along
U.ι, and its derived functor factors as the composite of the two exact derived
functors. Compare the chosen localization of the over-site with the standard
localization on U using uniqueness of localization and the derived universal
property. The residue square commutes by
Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField. The composition comparison
for derived pullback therefore identifies restriction followed by pullback to x
with pullback to U.ι(x) followed by pullback along Spec of the residue-field map.
For an open immersion the residue-field map is an isomorphism. Its tensor pullback
is an exact equivalence, so its derived functor commutes naturally with homology.
Comparing the supplied localization on the original residue scheme with the
standard localization on the new residue scheme gives the displayed comparison.
These comparisons descend from K-flat representatives by their universal properties,
so they are natural for arbitrary unbounded derived objects. No global-sections or
module-scalar comparison is included here. The empty open has no x, and no flatness
or perfectness hypothesis on the object is used. -/
theorem nonempty_localizedResidueHomology_sheaf_restriction_iso (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ s : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField s)).toRingedSpace))]
    (U : S.Opens) (x : U.toScheme) :
    letI : HasDerivedCategory.{u + 1} U.toScheme.Modules :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
        (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) :=
      HasDerivedCategory.standard _
    letI : (Scheme.Modules.overEquiv U).functor.Additive :=
      Functor.additive_of_preserves_binary_products _
    Nonempty
      ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory ⋙
        (Scheme.Modules.overEquiv U).functor.mapDerivedCategory.{w, u + 1} ⋙
        derivedPullback.{u, u + 1} (U.toScheme.fromSpecResidueField x) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)) 0 ≅
      derivedPullback (S.fromSpecResidueField (U.ι x)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace)) 0 ⋙
        Scheme.Modules.tensorPullback (Spec.map (U.ι.residueFieldMap x))) := by
  classical
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let O := SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)
  let B := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let C := SheafOfModules.{u} (moduleRings (Spec (S.residueField (U.ι x))).toRingedSpace)
  let D := SheafOfModules.{u} (moduleRings (Spec (U.toScheme.residueField x)).toRingedSpace)
  let hA : HasDerivedCategory.{w} A := inferInstance
  let hO : HasDerivedCategory.{w} O := inferInstance
  let hC : HasDerivedCategory.{w} C := inferInstance
  let hB := HasDerivedCategory.standard B
  let hD := HasDerivedCategory.standard D
  let : HasDerivedCategory.{u + 1} B := hB
  let : HasDerivedCategory.{u + 1} D := hD
  let R : A ⥤ O := SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U
  let E : O ⥤ B := (Scheme.Modules.overEquiv U).functor
  let : E.Additive := Functor.additive_of_preserves_binary_products _
  have : E.IsEquivalence := by dsimp [E]; infer_instance
  have : Limits.PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : Limits.PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let F := @Functor.mapDerivedCategory _ _ _ hA _ _ _ hO R _ _ _ ⋙
    @Functor.mapDerivedCategory _ _ _ hO _ _ _ hB E _ _ _
  have : Limits.PreservesFiniteLimits (R ⋙ E) := Limits.comp_preservesFiniteLimits _ _
  have : Limits.PreservesFiniteColimits (R ⋙ E) := Limits.comp_preservesFiniteColimits _ _
  let combined := @Functor.mapDerivedCategory _ _ _ hA _ _ _ hB (R ⋙ E) _ _ _
  let comp : combined ≅ F := (Functor.mapDerivedCategoryCompIso R E).symm
  let g := S.fromSpecResidueField (U.ι x)
  let r := Spec.map (U.ι.residueFieldMap x)
  let T : C ⥤ D := Scheme.Modules.tensorPullback r
  let L := @derivedPullback _ _ g hA hC
  let Lx := @derivedPullback _ _ (U.toScheme.fromSpecResidueField x) hB hD
  let HC := @DerivedCategory.homologyFunctor _ _ _ hC 0
  let HD := @DerivedCategory.homologyFunctor _ _ _ hD 0
  change Nonempty (F ⋙ Lx ⋙ HD ≅ L ⋙ HC ⋙ T)
  let sA := HasDerivedCategory.standard A
  let sO := HasDerivedCategory.standard O
  let sC := HasDerivedCategory.standard C
  let : ∀ X : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} A := sA
  let : HasDerivedCategory.{u + 1} O := sO
  let : HasDerivedCategory.{u + 1} B := hB
  let : HasDerivedCategory.{u + 1} C := sC
  let : HasDerivedCategory.{u + 1} D := hD
  let eA := (Localization.uniq (@DerivedCategory.Qh _ _ _ hA)
    (@DerivedCategory.Qh _ _ _ sA) (HomotopyCategory.quasiIso A (.up ℤ))).functor
  let eC := (Localization.uniq (@DerivedCategory.Qh _ _ _ hC)
    (@DerivedCategory.Qh _ _ _ sC) (HomotopyCategory.quasiIso C (.up ℤ))).functor
  obtain ⟨α⟩ := exact_source_transport (R ⋙ E) hA sA hB
  let first : F ≅ eA ⋙ (R ⋙ E).mapDerivedCategory :=
    comp.symm ≪≫ α
  let η : (Scheme.Modules.tensorPullback U.ι : A ⥤ B) ≅ R ⋙ E :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm ≪≫
      (Scheme.Modules.overFunctorEquiv U).symm
  have : Limits.PreservesFiniteLimits (Scheme.Modules.tensorPullback U.ι : A ⥤ B) :=
    Limits.preservesFiniteLimits_of_natIso η.symm
  have : Limits.PreservesFiniteColimits (Scheme.Modules.tensorPullback U.ι : A ⥤ B) :=
    Limits.preservesFiniteColimits_of_natIso η.symm
  have : (Scheme.Modules.tensorPullback U.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨openCompare⟩ := exact_pullback U.ι
  let openIso : (R ⋙ E).mapDerivedCategory ≅ derivedPullback U.ι :=
    (@Functor.mapDerivedCategoryNatIso A B _ _ _ _ sA hB
      (Scheme.Modules.tensorPullback U.ι) (R ⋙ E) _ _ _ _ _ _ η).symm ≪≫ openCompare.symm
  obtain ⟨_, _, _, c, _⟩ := exists_derivedPullbackComposition
  have square : r ≫ g = U.toScheme.fromSpecResidueField x ≫ U.ι :=
    U.ι.SpecMap_residueFieldMap_fromSpecResidueField x
  let residueIso : derivedPullback U.ι ⋙ Lx ≅ derivedPullback g ⋙ derivedPullback r :=
    c _ _ ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) square.symm) ≪≫ (c r g).symm
  have : T.IsEquivalence := tensorPullback_iso_equivalence (asIso r)
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨exactCompare⟩ := exact_pullback r
  obtain ⟨β⟩ := pullback_transport g hC hA sC sA
  obtain ⟨γ⟩ := homology_transport C hC sC 0
  let core : (R ⋙ E).mapDerivedCategory ⋙ Lx ⋙ HD ≅
      derivedPullback g ⋙ DerivedCategory.homologyFunctor C 0 ⋙ T :=
    Functor.isoWhiskerRight openIso (Lx ⋙ HD) ≪≫
      Functor.isoWhiskerRight residueIso HD ≪≫
      Functor.isoWhiskerLeft (derivedPullback g)
        (Functor.isoWhiskerRight exactCompare HD ≪≫
          (T.mapDerivedCategoryHomologyFunctorIso 0).symm)
  exact ⟨Functor.isoWhiskerRight first (Lx ⋙ HD) ≪≫
    Functor.isoWhiskerLeft eA core ≪≫
    Functor.isoWhiskerRight β.symm (DerivedCategory.homologyFunctor C 0 ⋙ T) ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight γ T)⟩

end AlgebraicGeometry
