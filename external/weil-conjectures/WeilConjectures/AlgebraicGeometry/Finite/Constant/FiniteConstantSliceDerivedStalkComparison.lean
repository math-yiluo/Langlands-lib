/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Constant complexes under the geometric stalk of a ringed slice

Source: Stacks Project, Tags 03CY, 0F6B, 00Y8(3), and 05RU.
(blueprint: lem-weil-pbc-finite-constant-slice-derived-stalk-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
/- The scalar and slice constructions below follow the proved implementation
in FiniteCoefficientSliceModelTransport. They are private proof helpers. -/
namespace FiniteConstantSliceStalkProof

section Scalars
universe a b
variable {C : Type a} [Category.{b} C] (J : GrothendieckTopology C)
  (Λ : Type (max a b)) [CommRing Λ]

/-- Restriction to constant scalars preserves the underlying additive sheaf exactly. -/
private def scalarRestriction (R : Sheaf J RingCat.{max a b})
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj) :
    SheafOfModules.{max a b} R ⥤
      Sheaf J (ModuleCat.{max a b} Λ) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars α).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{max a b} Λ :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars
      α).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private def constantModulePresheaf :
    (Cᵒᵖ ⥤ ModuleCat.{max a b} Λ) ⥤
      PresheafOfModules.{max a b}
        ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) where
  obj F :=
    { obj := F.obj
      map f := F.map f
      map_id U := by ext x; exact ConcreteCategory.congr_hom (F.map_id U) x
      map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map φ :=
    { app := φ.app
      naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }

private noncomputable def constantModuleFullyFaithful :
    (constantModulePresheaf (C := C) Λ).FullyFaithful where
  preimage φ :=
    { app := φ.app
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (φ.naturality f) x }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

private noncomputable instance : (constantModulePresheaf (C := C) Λ).Full :=
  (constantModuleFullyFaithful (C := C) Λ).full

private noncomputable instance : (constantModulePresheaf (C := C) Λ).Faithful :=
  (constantModuleFullyFaithful (C := C) Λ).faithful

private noncomputable def moduleEmbedding :=
  sheafToPresheaf J (ModuleCat.{max a b} Λ) ⋙
    constantModulePresheaf (C := C) Λ

private noncomputable instance : (moduleEmbedding J Λ).Full :=
  inferInstanceAs (sheafToPresheaf J
    (ModuleCat.{max a b} Λ) ⋙ constantModulePresheaf (C := C) Λ).Full

private noncomputable instance : (moduleEmbedding J Λ).Faithful :=
  inferInstanceAs (sheafToPresheaf J
    (ModuleCat.{max a b} Λ) ⋙ constantModulePresheaf (C := C) Λ).Faithful

variable (R : Sheaf J RingCat.{max a b})
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{max a b}] [J.WEqualsLocallyBijective AddCommGrpCat.{max a b}]

private noncomputable instance restriction_full : (scalarRestriction J Λ R α).Full := by
  exact Functor.Full.of_comp_faithful_iso
    (G := moduleEmbedding J Λ)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars α) (Iso.refl _)

private noncomputable instance restriction_faithful :
    (scalarRestriction J Λ R α).Faithful := by
  exact Functor.Faithful.of_comp_iso
    (G := moduleEmbedding J Λ)
    (H := SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars α) (Iso.refl _)

private noncomputable instance restriction_essSurj :
    (scalarRestriction J Λ R α).EssSurj where
  mem_essImage F := by
    let P := (moduleEmbedding J Λ).obj F
    let adj := PresheafOfModules.sheafificationAdjunction.{max a b}
      α
    have hη : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify J P.presheaf)
      exact isIso_toSheafify J
        ((sheafCompose J
          (forget₂ (ModuleCat.{max a b} Λ)
            AddCommGrpCat.{max a b})).obj F).property
    refine ⟨(PresheafOfModules.sheafification.{max a b} α).obj P, ⟨?_⟩⟩
    exact (Functor.FullyFaithful.ofFullyFaithful (moduleEmbedding J Λ)).preimageIso
      (asIso (adj.unit.app P)).symm

private instance scalarRestriction_equivalence :
    (scalarRestriction J Λ R α).IsEquivalence := by
  exact {}

private def constantExtension := moduleEmbedding J Λ ⋙
  PresheafOfModules.sheafification.{max a b} α

private def scalarCounit : scalarRestriction J Λ R α ⋙ constantExtension J Λ R α ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ asIso ((PresheafOfModules.sheafificationAdjunction.{max a b} α).counit.app M))
    (fun f ↦ (PresheafOfModules.sheafificationAdjunction.{max a b} α).counit.naturality f)

private instance constantExtension_equivalence :
    (constantExtension J Λ R α).IsEquivalence := by
  have : (scalarRestriction J Λ R α ⋙ constantExtension J Λ R α).IsEquivalence :=
    Functor.isEquivalence_of_iso (scalarCounit J Λ R α).symm
  exact Functor.isEquivalence_of_comp_left (scalarRestriction J Λ R α) _

private def scalarUnit : constantExtension J Λ R α ⋙ scalarRestriction J Λ R α ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (constantExtension J Λ R α)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (scalarCounit J Λ R α) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

variable [HasSheafify J (ModuleCat.{max a b} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{max a b} Λ)]

private def constantExtensionMap :
    ((Functor.const Cᵒᵖ) ⋙ constantModulePresheaf (C := C) Λ) ⋙
      PresheafOfModules.sheafification.{max a b} α ⟶
    constantSheaf J (ModuleCat.{max a b} Λ) ⋙ constantExtension J Λ R α :=
  Functor.whiskerRight (Functor.whiskerRight
    (Functor.whiskerLeft (Functor.const Cᵒᵖ)
      (sheafificationAdjunction J (ModuleCat.{max a b} Λ)).unit)
        (constantModulePresheaf (C := C) Λ))
    (PresheafOfModules.sheafification.{max a b} α)

private instance constantExtensionMap_isIso : IsIso (constantExtensionMap J Λ R α) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hw : (J.W.inverseImage (PresheafOfModules.toPresheaf.{max a b} _))
      ((constantModulePresheaf (C := C) Λ).map
        (toSheafify J ((Functor.const Cᵒᵖ).obj M))) := by
    change J.W (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b}))
    have : Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b})) := by
      apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
      change Presheaf.IsLocallyInjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (CategoryTheory.forget (ModuleCat.{max a b} Λ)))
      infer_instance
    have : Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (forget₂ (ModuleCat.{max a b} Λ) AddCommGrpCat.{max a b})) := by
      apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
      change Presheaf.IsLocallySurjective J
        (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj M))
          (CategoryTheory.forget (ModuleCat.{max a b} Λ)))
      infer_instance
    exact J.W_of_isLocallyBijective _
  rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α] at hw
  exact hw

private def constantScalarIso :
    (((Functor.const Cᵒᵖ) ⋙ constantModulePresheaf (C := C) Λ) ⋙
      PresheafOfModules.sheafification.{max a b} α) ⋙ scalarRestriction J Λ R α ≅
        constantSheaf J (ModuleCat.{max a b} Λ) :=
  Functor.isoWhiskerRight (asIso (constantExtensionMap J Λ R α)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (scalarUnit J Λ R α) ≪≫ Functor.rightUnitor _

end Scalars

section Coordinates

attribute [local irreducible] completedAdicChangeData pbcDerivedScalarAdjunction

variable (X : Scheme.{t}) (B : Type t) [CommRing B]
  (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ R)

private abbrev moduleRing :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

private def scalarMap :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶
      (moduleRing X R).obj :=
  koszulConstantUnit X B ≫
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ).hom

private def sliceCoordinates (W : X.Etale) :
    SheafOfModules.{t + 1} ((moduleRing X R).over ((toProEt X).obj W)) ⥤
      Sheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B)) := by
  let U := (toProEt X).obj W
  have : (ProEt.sliceEquiv X U).inverse.IsDenseSubsite
      (ProEt.topology W.left) ((ProEt.topology X).over U) := ProEt.sliceDense X U
  exact scalarRestriction ((ProEt.topology X).over U) (ULift.{t + 1} B)
    ((moduleRing X R).over U) (Functor.whiskerLeft (Over.forget U).op (scalarMap X B R φ)) ⋙
    ((ProEt.sliceEquiv X U).sheafCongr ((ProEt.topology X).over U)
      (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B))).functor

private def sliceCoordinatesSquare (W : X.Etale) :
    SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W) ⋙
        sliceCoordinates X B R φ W ≅ finiteCoefficientSliceRestriction X B R φ W :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private instance sliceCoordinates_equivalence [IsIso φ] (W : X.Etale) :
    (sliceCoordinates X B R φ W).IsEquivalence := by
  let U := (toProEt X).obj W
  have := ProEt.sliceDense X U
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have := Presheaf.isLocallyInjective_whisker ((ProEt.topology X).over U)
    (ProEt.topology X) (Over.forget U) (scalarMap X B R φ)
  have := Presheaf.isLocallySurjective_whisker ((ProEt.topology X).over U)
    (ProEt.topology X) (Over.forget U) (scalarMap X B R φ)
  dsimp only [sliceCoordinates]
  infer_instance

private instance sliceCoordinates_additive [IsIso φ] (W : X.Etale) :
    (sliceCoordinates X B R φ W).Additive :=
  Functor.additive_of_preserves_binary_products _

private instance over_additive (W : X.Etale) :
    (SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)).Additive where
  map_add := by intros; rfl

private theorem over_limits [IsIso φ] (W : X.Etale) :
    PreservesFiniteLimits
      (SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)) := by
  let O := SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)
  let E := sliceCoordinates X B R φ W
  have := (finiteCoefficientSliceRestriction_exact X B R φ W).2.1
  have : PreservesFiniteLimits (O ⋙ E) :=
    preservesFiniteLimits_of_natIso (sliceCoordinatesSquare X B R φ W).symm
  exact preservesFiniteLimits_of_reflects_of_preserves O E

private theorem over_colimits [IsIso φ] (W : X.Etale) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)) := by
  let O := SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)
  let E := sliceCoordinates X B R φ W
  have := (finiteCoefficientSliceRestriction_exact X B R φ W).2.2
  have : PreservesFiniteColimits (O ⋙ E) :=
    preservesFiniteColimits_of_natIso (sliceCoordinatesSquare X B R φ W).symm
  exact preservesFiniteColimits_of_reflects_of_preserves O E

private def restrictionCoordinatesIso [IsIso φ] (W : X.Etale)
    (K : DerivedCategory (SheafOfModules.{t + 1} (moduleRing X R))) :
    (sliceCoordinates X B R φ W).mapDerivedCategory.obj
        (ringedSiteDerivedRestrictionOfUniverses (moduleRing X R) ((toProEt X).obj W) K) ≅
      (finiteCoefficientSliceRestriction X B R φ W).mapDerivedCategory.obj K := by
  have := (finiteCoefficientSliceRestriction_exact X B R φ W).1
  have := (finiteCoefficientSliceRestriction_exact X B R φ W).2.1
  have := (finiteCoefficientSliceRestriction_exact X B R φ W).2.2
  have := over_limits X B R φ W
  have := over_colimits X B R φ W
  let O := SheafOfModules.overFunctor.{t + 1} (moduleRing X R) ((toProEt X).obj W)
  let E := sliceCoordinates X B R φ W
  let e : O.mapDerivedCategory.obj K ≅
      ringedSiteDerivedRestrictionOfUniverses (moduleRing X R) ((toProEt X).obj W) K :=
    (O.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      O.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)
  exact E.mapDerivedCategory.mapIso e.symm ≪≫
    (Functor.mapDerivedCategoryCompIso O E).app K ≪≫
      (Functor.mapDerivedCategoryNatIso (sliceCoordinatesSquare X B R φ W)).app K

private def globalScalarIso :
    SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ) ⋙
      proEtaleModuleRestriction X B ≅
        scalarRestriction (ProEt.topology X) (ULift.{t + 1} B)
          (moduleRing X R) (scalarMap X B R φ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private instance scalarRestrictionIso_equivalence [IsIso φ] :
    (SheafOfModules.restrictScalars.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
    ).IsEquivalence := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  have : Presheaf.IsLocallyInjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have : Presheaf.IsLocallySurjective (ProEt.topology X) (scalarMap X B R φ) := by
    unfold scalarMap
    infer_instance
  have := proEtaleModuleRestriction_isEquivalence X B
  have := Functor.isEquivalence_of_iso (globalScalarIso X B R φ).symm
  exact Functor.isEquivalence_of_comp_right _ (proEtaleModuleRestriction X B)

private def koszulConstantScalarIso :
    koszulConstantFunctor X B ⋙ proEtaleModuleRestriction X B ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} B)) := by
  have := (koszulConstantUnit_local X B).1
  have := (koszulConstantUnit_local X B).2
  exact constantScalarIso (ProEt.topology X) (ULift.{t + 1} B)
    (adicModuleRing X B) (koszulConstantUnit X B)

private theorem derivedScalarUnit [IsIso φ] :
    Nonempty (𝟭 (DerivedCategory (SheafOfModules.{t + 1} (adicModuleRing X B))) ≅
      completedAdicDerivedChange X φ ⋙
        (SheafOfModules.restrictScalars.{t + 1}
          ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
        ).mapDerivedCategory) := by
  let U := pbcRestrict φ
  have : U.IsEquivalence := inferInstance
  have : (pbcDerivedRestrict φ).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory U
  exact ⟨asIso (pbcDerivedScalarAdjunction φ).unit⟩

private def constantLocalizationIso (W : X.Etale) :
    constantSheaf (ProEt.topology X) (ModuleCat.{t + 1} (ULift.{t + 1} B)) ⋙
        ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B))
          W.hom inferInstance ≅
      constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B)) := by
  let G := MorphismProperty.Over.map (f := W.hom) ⊤
    (inferInstance : WeaklyEtale W.hom)
  have : G.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale W.hom)
  have : G.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale W.hom)
  exact Functor.isoWhiskerLeft (Functor.const X.ProEtᵒᵖ)
    (G.pushforwardContinuousSheafificationCompatibility
      (ModuleCat.{t + 1} (ULift.{t + 1} B))
        (ProEt.topology W.left) (ProEt.topology X)).symm

private theorem constantModelIso [IsIso φ]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (W : X.Etale) (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty ((finiteCoefficientSliceRestriction X B R φ W).mapDerivedCategory.obj
        ((completedAdicDerivedChange X φ).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) ≅
      DerivedCategory.Q.obj
        (((constantSheaf (ProEt.topology W.left)
          (ModuleCat.{t + 1} (ULift.{t + 1} B))).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
            ModuleCat.restrictScalars.{t + 1}
              (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
            ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  obtain ⟨eUnit⟩ := derivedScalarUnit X B R φ
  let U := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
  let H := proEtaleModuleRestriction X B
  have := proEtaleModuleRestriction_isEquivalence X B
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  let S := ProEtale.localizationRestriction
    (ModuleCat.{t + 1} (ULift.{t + 1} B)) W.hom inferInstance
  have : S.Additive := { map_add := by intros; rfl }
  have : PreservesFiniteLimits S := by
    dsimp only [S, ProEtale.localizationRestriction]
    infer_instance
  have := (ProEtale.localizationRestrictionLowerStarAdjunction
    (ModuleCat.{t + 1} (ULift.{t + 1} B)) W.hom inferInstance).isLeftAdjoint
  let Pu := ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex (.up ℤ)).obj P
  let e : koszulConstantFunctor X B ⋙ (H ⋙ S) ≅
      constantSheaf (ProEt.topology W.left) (ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
    Functor.isoWhiskerRight (koszulConstantScalarIso X B) S ≪≫
      constantLocalizationIso X B W
  exact ⟨((Functor.mapDerivedCategoryCompIso U (H ⋙ S)).app _).symm ≪≫
    (H ⋙ S).mapDerivedCategory.mapIso
      ((eUnit.app (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))).symm) ≪≫
    (H ⋙ S).mapDerivedCategoryFactors.app (finiteModelConstantComplex X B P) ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (.up ℤ)).app Pu)⟩

end Coordinates

end FiniteConstantSliceStalkProof

/-- A geometric stalk on the slice recovers the lifted algebraic constant complex.
The same functor works for every complex; no isomorphism between two complexes is
assumed or reflected by this statement.

Source: Stacks Project, Modules on Sites, Tag 03CY; proetale.tex, Tag 0F6B;
Sites, Tag 00Y8(3); Derived Categories, Tag 05RU.
(blueprint: lem-weil-pbc-finite-constant-slice-derived-stalk-comparison).

Proof: identify X_proet/W with W_proet by composition of weakly etale maps.
Restriction along the coefficient isomorphism phi identifies modules over R|W
with modules over the restricted constant ring sheaf. Restriction along constant
sections then identifies these with ULift(B)-module-valued sheaves. Take the
geometric stalk at y and restrict scalars along B -> ULift(B). All these functors
are additive and exact: the coefficient transports are equivalences, and the
stalk is a filtered colimit with the usual local lifting property. Thus their
termwise composite descends at quasi-isomorphisms to a functor F on unbounded
derived categories. For a module M, the constant-section germ identifies the stalk
of the constant module sheaf with M. This identification is natural in all module
maps, so it identifies every differential of a constant complex as well. Extension
along phi cancels the first scalar restriction, since phi is an isomorphism;
its derived extension is its exact termwise extension by uniqueness of the derived
functor. The representative-based slice restriction agrees with exact derived
restriction through Q.objObjPreimageIso. Composing these comparisons gives the
claimed isomorphism with the termwise universe lift. This argument imposes no
bounds on P and works for the zero ring and zero complex. The supplied point y
is the only nonemptiness needed. -/
theorem finiteConstantSlice_derivedStalk_comparison
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    [HasDerivedCategory.{w} (ModuleCat.{t + 1} B)]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ)
    (W : X.Etale) {Ω : Type t} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ W.left) :
    ∃ F : DerivedCategory (SheafOfModules.{t + 1}
        (((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R).over
            ((toProEt X).obj W))) ⥤ DerivedCategory (ModuleCat.{t + 1} B),
      ∀ P : CochainComplex (ModuleCat.{t} B) ℤ,
        Nonempty (F.obj
          (ringedSiteDerivedRestrictionOfUniverses
            ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)
            ((toProEt X).obj W) ((completedAdicDerivedChange X φ).obj
              (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)))) ≅
          DerivedCategory.Q.obj
            (((ModuleCat.uliftFunctor.{t + 1, t} B).mapHomologicalComplex (.up ℤ)).obj P)) :=
  by
  let := hφ
  let A := ModuleCat.{t + 1} (ULift.{t + 1} B)
  let Φ := AlgebraicGeometry.ProEtale.geometricPoint y
  let S : Sheaf (ProEt.topology W.left) A ⥤ A := Φ.sheafFiber
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  let scalarEquiv : ModuleCat.{t + 1} B ≌ A :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B)
  let T := scalarEquiv.inverse
  have : T.IsLeftAdjoint := scalarEquiv.symm.isLeftAdjoint_functor
  have : T.IsRightAdjoint := scalarEquiv.isRightAdjoint_inverse
  -- Pass from the ringed slice to fixed-scalar sheaves on the chart.
  let E := FiniteConstantSliceStalkProof.sliceCoordinates X B R φ W
  have : E.IsEquivalence :=
    FiniteConstantSliceStalkProof.sliceCoordinates_equivalence X B R φ W
  have : E.Additive := Functor.additive_of_preserves_binary_products E
  refine ⟨E.mapDerivedCategory ⋙ S.mapDerivedCategory ⋙ T.mapDerivedCategory, ?_⟩
  intro P
  let Pu := ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom
    ).mapHomologicalComplex (.up ℤ)).obj P
  -- Cancel coefficient change and compute the resulting constant complex.
  obtain ⟨eModel⟩ := FiniteConstantSliceStalkProof.constantModelIso X B R φ W P
  let eSlice := FiniteConstantSliceStalkProof.restrictionCoordinatesIso X B R φ W
    ((completedAdicDerivedChange X φ).obj
      (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)))
  let eConstant : constantSheaf (ProEt.topology W.left) A ⋙ S ≅ 𝟭 A :=
    Φ.constantSheafCompSheafFiberIso (ProEt.topology W.left) A
  let eScalars : ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙ T ≅
        𝟭 (ModuleCat.{t + 1} B) :=
    scalarEquiv.unitIso.symm
  -- Exact localization, constant fibres, and the scalar-equivalence unit.
  refine ⟨T.mapDerivedCategory.mapIso
    (S.mapDerivedCategory.mapIso (eSlice ≪≫ eModel) ≪≫
      S.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex eConstant (.up ℤ)).app Pu)) ≪≫
    T.mapDerivedCategoryFactors.app Pu ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex
        (Functor.isoWhiskerLeft (ModuleCat.uliftFunctor.{t + 1, t} B) eScalars)
          (.up ℤ)).app P)⟩

end AlgebraicGeometry.Scheme
