/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement

/-!
# Unbounded ordinary etale compact-support comparisons

Source: Stacks Project, Tags 0F7H--0F7L and 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons).

The candidates, common-refinement comparisons, and proper/open tower isomorphism are the
existing ordinary etale constructions. The definitions below assemble the specified tower
composition and transport the existing exchange to exact, termwise inverse image. The
statements supply coherence and equality with the bounded-below maps, on actual natural
transformations rather than just existence of unrelated isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private lemma mate_ofNatIsoLeft
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂')
    (α : TwoSquare G L₁' L₂' H) :
    (mateEquiv (adj₁.ofNatIsoLeft e₁) (adj₂.ofNatIsoLeft e₂) α) =
      (mateEquiv adj₁ adj₂ ((α.whiskerRight e₂.hom).whiskerLeft e₁.inv)) := by
  ext K
  simp [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, Category.assoc, ← Functor.map_comp]

private lemma mate_whiskerTop
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H : D ⥤ F}
    (α : TwoSquare G' L₁ L₂ H) (γ : G ⟶ G') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerTop γ)).app K =
      γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α).app K := by
  simp [mateEquiv, TwoSquare.whiskerTop]

private lemma mate_whiskerBottom
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G : C ⥤ E} {H H' : D ⥤ F}
    (α : TwoSquare G L₁ L₂ H) (δ : H ⟶ H') (K : D) :
    (mateEquiv adj₁ adj₂ (α.whiskerBottom δ)).app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  simp [mateEquiv, TwoSquare.whiskerBottom, ← Functor.map_comp, δ.naturality]

set_option backward.isDefEq.respectTransparency false in
private lemma inverse_mates_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {F₁ : C ⥤ E} {U₁ : E ⥤ C} {F₂ : D ⥤ F} {U₂ : F ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : F₁ ⊣ U₁) (adj₄ : F₂ ⊣ U₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂)
    (α : TwoSquare U₁ L₂ L₁ U₂)
    (hα : ∀ K, adj₄.unit.app (L₁.obj K) ≫ U₂.map (e.hom.app K) =
      L₁.map (adj₃.unit.app K) ≫ α.app (F₁.obj K)) (K : D) :
    (adj₃.homEquiv _ _
      ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv)).app K)) ≫
      (mateEquiv adj₂ adj₁ α).app (F₂.obj K) = R₁.map (adj₄.unit.app K) := by
  let γ := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv))
  change (adj₃.homEquiv _ _ (γ.app K)) ≫ _ = _
  simp only [Adjunction.homEquiv_unit, mateEquiv_apply, NatTrans.comp_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  change adj₃.unit.app (R₁.obj K) ≫ U₁.map (γ.app K) ≫
    adj₁.unit.app (U₁.obj (R₂.obj (F₂.obj K))) ≫
    R₁.map (α.app (R₂.obj (F₂.obj K))) ≫
    R₁.map (U₂.map (adj₂.counit.app (F₂.obj K))) = _
  rw [reassoc_of% (adj₁.unit.naturality (U₁.map (γ.app K)))]
  rw [reassoc_of% (adj₁.unit.naturality (adj₃.unit.app (R₁.obj K)))]
  simp only [← R₁.map_comp]
  rw [reassoc_of% (α.naturality (γ.app K))]
  rw [← Category.assoc (L₁.map _) (α.app _) _, ← hα]
  rw [Category.assoc]
  rw [← U₂.map_comp (L₂.map (γ.app K)) (adj₂.counit.app (F₂.obj K))]
  rw [mateEquiv_counit]
  simp only [TwoSquare.mk, Functor.map_comp]
  have hc : R₁.map (U₂.map (e.hom.app (R₁.obj K))) ≫
      R₁.map (U₂.map (e.inv.app (R₁.obj K))) = 𝟙 _ := by
    rw [← R₁.map_comp, ← U₂.map_comp, Iso.hom_inv_id_app, U₂.map_id, R₁.map_id]
  rw [reassoc_of% hc]
  rw [← R₁.map_comp, adj₄.unit_naturality]
  rw [R₁.map_comp, adj₁.right_triangle_components_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exact_exchange_transport
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (rightDerivedLowerStar (ModuleCat.{u + 1} A) f)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
      derivedBaseChangeMap (ModuleCat.{u + 1} A) sq ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g').hom _ =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  let B := ModuleCat.{u + 1} A
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq).hom
  have hs :
      ((((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
        (leftDerivedUpperStarIsoMapDerivedCategory B g').inv).whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory B f').hom).whiskerLeft
        (leftDerivedUpperStarIsoMapDerivedCategory B f).inv) =
      TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso B sq).hom := by
    ext M
    simp only [α, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk]
    simp only [derivedSquareUpperStarIso, leftDerivedUpperStarComp,
      exactDerivedSquareUpperStarIso, squareUpperStarIso,
      Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.inv_hom_id_app_assoc]
    rw [← (upperStar B g').leftDerivedFunctorIsoMapDerivedCategory.inv.naturality]
  have hm := mate_ofNatIsoLeft
    (derivedUpperStarLowerStarAdjunction B f) (derivedUpperStarLowerStarAdjunction B f')
    (leftDerivedUpperStarIsoMapDerivedCategory B f)
    (leftDerivedUpperStarIsoMapDerivedCategory B f')
    ((α.whiskerTop (leftDerivedUpperStarIsoMapDerivedCategory B g).hom).whiskerBottom
      (leftDerivedUpperStarIsoMapDerivedCategory B g').inv)
  rw [← mapDerivedUpperStarLowerStarAdjunction_eq,
    ← mapDerivedUpperStarLowerStarAdjunction_eq, hs] at hm
  change _ = derivedBaseChangeMap B sq at hm
  rw [← hm]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [mate_whiskerBottom, mate_whiskerTop]
  change _ = (mateEquiv (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f') α).app K
  dsimp only [B, rightDerivedLowerStar, Functor.comp_obj]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

section UnboundedFormalism

private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

private lemma identity_tail_eq
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
        ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
          Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
            Functor.mapDerivedCategoryIdIso _) ≪≫ Functor.rightUnitor _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
            (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫ Functor.mapDerivedCategoryIdIso _ =
      identityEtaleCompactSupportComparison A X ≪≫
        Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
            (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫ Functor.mapDerivedCategoryIdIso _ := by
  unfold identityEtaleCompactSupportComparison
  simp only [Iso.trans_assoc]
  rfl

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

private noncomputable def exact_pb_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z := f ≫ g)
    (hfg : fg = f ≫ g := by cat_disch) :
    (upperStar (ModuleCat.{u + 1} A) fg).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)

private lemma exact_pb_comp_assoc
    (A : Type (u + 1)) [CommRing A] {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (exact_pb_comp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (exact_pb_comp A g h gh hgh).hom
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory =
      (exact_pb_comp A fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
          (exact_pb_comp A f g fg hfg).hom := by
  let B := ModuleCat.{u + 1} A
  have he : upperStarComp B fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (upperStar B h) (upperStarComp B f g fg hfg) =
      upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (upperStarComp B g h gh hgh) (upperStar B f) := by
    apply Iso.ext
    exact (upperStarComp_assoc' B f g h fg gh fgh hfg hgh hfgh).symm
  exact (derived_triangle_assoc (upperStar B h) (upperStar B g) (upperStar B f)
    (upperStar B gh) (upperStar B fg) (upperStar B fgh)
    (upperStarComp B g h gh hgh) (upperStarComp B f g fg hfg)
    (upperStarComp B fg h fgh hfgh)
    (upperStarComp B f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) he).symm

private lemma exact_pb_comp_congr
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (d d' : X ⟶ Z)
    (hd : d = f ≫ g) (hd' : d' = f ≫ g)
    (M : DerivedCategoryModule A Z) :
    (exact_pb_comp A f g d hd).hom.app M =
      eqToHom (by rw [hd, hd']) ≫ (exact_pb_comp A f g d' hd').hom.app M := by
  subst hd hd'
  simp

private noncomputable def exact_pb_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma exact_pb_id_left
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A (𝟙 X) f f (Category.id_comp f).symm).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
        (exact_pb_id A X).hom = 𝟙 _ := by
  apply derived_unit_right
  rw [upperStarComp_id_left]
  apply Iso.ext
  ext M
  simp

private lemma exact_pb_id_right
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exact_pb_comp A f (𝟙 Y) f (Category.comp_id f).symm).hom ≫
      Functor.whiskerRight (exact_pb_id A Y).hom
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory = 𝟙 _ := by
  apply derived_unit_left
  rw [upperStarComp_id_right]
  apply Iso.ext
  ext M
  simp

private noncomputable def unboundedFormalism
    (A : Type (u + 1)) [CommRing A] : CompactSupportFormalism where
  obj X := DerivedCategoryModule A X
  category X := inferInstanceAs (Category.{u + 1} (DerivedCategoryModule A X))
  pb f := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  pbId X := exact_pb_id A X
  pbComp f g := exact_pb_comp A f g
  pbComp_assoc f g h M := by
    have hh := NatTrans.congr_app
      (exact_pb_comp_assoc A f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hh
    rw [← hh, exact_pb_comp_congr A f (g ≫ h) _ (f ≫ g ≫ h)
      (Category.assoc _ _ _) rfl]
    simp only [Category.assoc, Functor.comp_obj]
  pbId_comp f M := by
    have hh := NatTrans.congr_app (exact_pb_id_left A f) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A (𝟙 _) f _ f rfl (Category.id_comp f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pbComp_id f M := by
    have hh := NatTrans.congr_app (exact_pb_id_right A f) M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at hh
    rw [exact_pb_comp_congr A f (𝟙 _) _ f rfl (Category.comp_id f).symm]
    rw [Category.assoc, hh]
    simp only [Category.comp_id]
  pf f := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  adj f := mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  sh j hj := haveI := hj.out; (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  shAdj j hj := haveI := hj.out; (openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction

private lemma derived_square_symm
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {P : C ⥤ D} {Q : D ⥤ F} {R : C ⥤ E} {S : E ⥤ F}
    [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : P ⋙ Q ≅ R ⋙ S) :
    Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]

private lemma open_exchange_mate_coefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction B r
          ).mapDerivedCategoryAdjunction
        (openImmersionLowerShriekUpperStarAdjunction B l
          ).mapDerivedCategoryAdjunction).symm
        (TwoSquare.mk _ _ _ _
          (exactDerivedSquareUpperStarIso B sq.toCommSq).inv)) := by
  let := isIso_openImmersionLowerShriekBaseChangeMap B sq
  have h := mateEquiv_eq_of_unit
    (openImmersionLowerShriekUpperStarAdjunction B r).mapDerivedCategoryAdjunction
    (openImmersionLowerShriekUpperStarAdjunction B l).mapDerivedCategoryAdjunction
    (TwoSquare.mk _ _ _ _ (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).hom)
    (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).inv) (fun K ↦ ?_)
  · exact (((mateEquiv _ _).symm_apply_eq.mpr h.symm)).symm
  have hK := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction B r)
    (openImmersionLowerShriekUpperStarAdjunction B l)
    (squareUpperStarIso B sq.toCommSq.flip)
    (asIso (openImmersionLowerShriekBaseChangeMap B sq.toCommSq))
    (unit_map_openImmersionLowerShriekBaseChangeMap_app B sq.toCommSq) K
  rewrite [squareUpperStarIso_flip, derived_square_symm] at hK
  exact hK.symm

private lemma unbounded_pb_comp'
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : f ≫ g = fg) :
    (unboundedFormalism A).pbComp' f g fg w = exact_pb_comp A f g fg w.symm := by
  subst w
  rw [ExchangeFormalism.pbComp'_rfl]
  rfl

private lemma unbounded_sq_iso
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} (sq : CommSq t l r b) :
    (unboundedFormalism A).sqIso t l r b sq.w =
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).symm := by
  apply Iso.ext
  simp only [ExchangeFormalism.sqIso, unbounded_pb_comp', exact_pb_comp,
    Functor.mapDerivedCategoryTriangleIso, exactDerivedSquareUpperStarIso,
    squareUpperStarIso, derived_iso_trans,
    derived_iso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc]

private lemma unbounded_pf_base_change
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} (sq : CommSq t l r b) :
    ((unboundedFormalism A).pfBaseChange t l r b sq.w) =
      exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq := by
  rw [ExchangeFormalism.pfBaseChange, unbounded_sq_iso]
  rfl

private lemma unbounded_open_base_change
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    ((unboundedFormalism A).baseChange t l r b sq.w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).hom := by
  rw [ExchangeFormalism.baseChange, unbounded_sq_iso]
  exact (open_exchange_mate_coefficients (ModuleCat.{u + 1} A) sq).symm

private local instance unbounded_has_base_change
    (A : Type (u + 1)) [CommRing A] : (unboundedFormalism A).HasBaseChange where
  isIso_baseChange sq := by
    rw [unbounded_open_base_change A sq]
    infer_instance

private lemma unbounded_open_exchange
    (A : Type (u + 1)) [CommRing A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    haveI := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := unboundedFormalism A) sq
    ((unboundedFormalism A).exchange t l r b sq.w) =
      openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) sq
  dsimp only [ExchangeFormalism.exchange, openImmersionLowerShriekLowerStarExchange]
  have hh : inv ((unboundedFormalism A).baseChange t l r b sq.w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) sq).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change A sq]
    exact Iso.hom_inv_id _
  rw [hh]
  rfl

private local instance unbounded_has_proper_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    (unboundedFormalism A).HasProperExchange where
  isIso_exchange sq := by
    rw [unbounded_open_exchange A sq]
    exact isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
      isAddTorsion_of_finite sq

private lemma unbounded_pf_comp_inv
    (A : Type (u + 1)) [CommRing A] {T S R : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ R) (fg : T ⟶ R) (w : f ≫ g = fg) :
    ((unboundedFormalism A).pfComp' f g fg w).inv =
      (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) f)
        (lowerStar (ModuleCat.{u + 1} A) g)
        (lowerStarComp (ModuleCat.{u + 1} A) f g fg w.symm)).hom := by
  let B := ModuleCat.{u + 1} A
  have hh := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B g)
    (upperStarLowerStarAdjunction B fg) (lowerStarComp B f g fg w.symm)
    (upperStarComp B f g fg w.symm) (by
      exact (congrArg Iso.hom
        (conjugateIsoEquiv_upperStarComp B f g fg w.symm)).symm)
  rw [ExchangeFormalism.pfComp', unbounded_pb_comp']
  exact hh.symm

section ExactOpenComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe vC vD vE uC uD uE wC wD wE

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma exact_unit_ext
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {F G : DerivedCategory C ⥤ DerivedCategory C} {α β : F ⟶ G}
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      α.app (DerivedCategory.Qh.obj K) = β.app (DerivedCategory.Qh.obj K)) : α = β := by
  exact Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) h

private lemma exact_adj_conjugate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (r : R₂ ≅ R₁)
    (h : ∀ K, a.unit.app K ≫ R₁.map (e.hom.app K) =
      b.unit.app K ≫ r.hom.app (L₂.obj K)) :
    a.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom R₁.mapDerivedCategory =
      b.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerLeft L₂.mapDerivedCategory (Functor.mapDerivedCategoryNatIso r).hom := by
  apply exact_unit_ext (C := C)
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map (L₂.mapDerivedCategoryFactorsh.hom.app K) ≫
    R₁.mapDerivedCategoryFactorsh.hom.app ((L₂.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  have he := Functor.mapDerivedCategoryNatIso_fach e K
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, he, Functor.map_comp]
  have hNR := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K)
  simp only [Functor.comp_map] at hNR
  simp only [Category.assoc]
  erw [hNR]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  have hN := (Functor.mapDerivedCategoryNatIso r).hom.naturality
    (L₂.mapDerivedCategoryFactorsh.hom.app K)
  erw [← reassoc_of% hN]
  erw [Functor.mapDerivedCategoryNatIso_fach r]
  erw [reassoc_of% (b.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) a b e.hom r.hom h K
end ExactOpenComposition

section IdentityComparisons
universe vC vD uC uD wC wD v w
attribute [local irreducible] Adjunction.mapDerivedCategoryAdjunction
private lemma exact_adj_id
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    (Adjunction.id (C := C)).mapDerivedCategoryAdjunction =
      ((Adjunction.id (C := DerivedCategory C)).ofNatIsoLeft
        (Functor.mapDerivedCategoryIdIso C).symm).ofNatIsoRight
        (Functor.mapDerivedCategoryIdIso C).symm := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Category.id_comp]
  rw [← cancel_mono ((𝟭 C).mapDerivedCategory.map
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K) ≫
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app
        (((𝟭 C).mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  erw [(Adjunction.id (C := C)).mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := (Functor.mapDerivedCategoryIdIso C).inv.naturality
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn]
  rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  rw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Iso.inv_hom_id_app]
  rw [Adjunction.mapHomotopyCategory_id_unit_app]
  have hi (K' : HomotopyCategory C (.up ℤ)) :
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).inv.app K' = 𝟙 K' := by
    apply (cancel_mono ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K')).mp
    erw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
      Category.id_comp]
    rfl
  erw [hi]
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact DerivedCategory.Qh.map_id K
private lemma identity_conjugate_of_unit
    {C : Type*} [Category C] {L R I : C ⥤ C}
    (a : L ⊣ R) (δ : I ≅ 𝟭 C) (e : L ≅ I) (r : R ≅ I)
    (h : a.unit ≫ Functor.whiskerRight e.hom R =
      (((Adjunction.id (C := C)).ofNatIsoLeft δ.symm).ofNatIsoRight δ.symm).unit ≫
        Functor.whiskerLeft I r.inv) :
    conjugateEquiv Adjunction.id a (e ≪≫ δ).hom = (r ≪≫ δ).inv := by
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := NatTrans.congr_app h K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Adjunction.id_unit,
    Functor.id_map, Category.id_comp] at hK
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.map_comp]
  rw [← Category.assoc, hK]
  simp only [Category.assoc]
  rw [← (r.inv.naturality (δ.hom.app K))]
  rw [← reassoc_of% (δ.inv.naturality (δ.hom.app K))]
  simp only [ ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

private lemma derived_open_id_conjugate
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateEquiv Adjunction.id
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
        ).mapDerivedCategoryAdjunction
      (Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom =
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv := by
  let B := ModuleCat.{u + 1} A
  let a := openImmersionLowerShriekUpperStarAdjunction B (𝟙 X)
  let e := Adjunction.leftAdjointIdIso a (upperStarId B X)
  have hu (K : Sheaf X.smallEtaleTopology B) :
      a.unit.app K ≫ (upperStar B (𝟙 X)).map (e.hom.app K) =
        Adjunction.id.unit.app K ≫ (upperStarId B X).inv.app K := by
    have h := unit_conjugateEquiv Adjunction.id a e.hom K
    simpa only [Adjunction.conjugateEquiv_leftAdjointIdIso_hom, e,
      Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj, Category.id_comp]
      using h.symm
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf X.smallEtaleTopology B)
    a Adjunction.id e (upperStarId B X).symm hu
  rw [exact_adj_id (C := Sheaf X.smallEtaleTopology B)] at hd
  apply identity_conjugate_of_unit
  simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd
private lemma exact_right_adj
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    [L₁.Additive] [R₁.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    (a : L₁ ⊣ R₁) :
    a.mapDerivedCategoryAdjunction =
      a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R₁.rightDerivedFunctorIsoMapDerivedCategory := by
  apply Adjunction.ext
  apply exact_unit_ext (C := C)
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map
    (L₁.mapDerivedCategoryFactorsh.hom.app K) ≫
      R₁.mapDerivedCategoryFactorsh.hom.app ((L₁.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  rw [a.mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := R₁.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L₁.mapDerivedCategoryFactorsh.hom.app K)
  rw [← reassoc_of% hn]
  have hη := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L₁.mapDerivedCategoryFactorsh.hom
    R₁.rightDerivedFunctorUnit K
  erw [reassoc_of% hη]
  have hR := NatTrans.congr_app R₁.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L₁.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hR
  rw [← Category.assoc _ _ (R₁.mapDerivedCategoryFactorsh.hom.app _), hR,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

private lemma right_identity_conjugate
    {C : Type*} [Category C] {L R S : C ⥤ C}
    (a : L ⊣ R) (κ : R ≅ S) (e : L ≅ 𝟭 C) (r : S ≅ 𝟭 C)
    (h : conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom = r.inv) :
    conjugateIsoEquiv a Adjunction.id e.symm = κ ≪≫ r := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro K
  have hu := unit_conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom K
  rw [h] at hu
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.id_unit, NatTrans.id_app,
    Category.id_comp] at hu
  have ht := congrArg (fun t ↦ t ≫ S.map (e.inv.app K) ≫ r.hom.app (L.obj K)) hu
  simp only [Category.assoc] at ht
  rw [← S.map_comp_assoc, Iso.hom_inv_id_app, S.map_id, Category.id_comp] at ht
  rw [r.hom.naturality (e.inv.app K)] at ht
  simp only [Functor.id_obj, Functor.id_map, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp] at ht
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj,
    Category.id_comp, Category.assoc] using ht.symm

private lemma derived_star_id_conjugate
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    conjugateIsoEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
      Adjunction.id
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm =
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
  let B := ModuleCat.{u + 1} A
  have hu (K : Sheaf X.smallEtaleTopology B) :
      (upperStarLowerStarAdjunction B (𝟙 X)).unit.app K ≫
        (lowerStar B (𝟙 X)).map ((upperStarId B X).hom.app K) =
      Adjunction.id.unit.app K ≫ (lowerStarId B X).inv.app K := by
    simpa only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] using
      upperStarId_hom_app_unit_app B X K
  have hd := exact_adj_conjugate
    (C := Sheaf X.smallEtaleTopology B) (D := Sheaf X.smallEtaleTopology B)
    (upperStarLowerStarAdjunction B (𝟙 X))
    Adjunction.id (upperStarId B X) (lowerStarId B X).symm hu
  rw [exact_adj_id (C := Sheaf X.smallEtaleTopology B)] at hd
  have he := identity_conjugate_of_unit
    (upperStarLowerStarAdjunction B (𝟙 X)).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (upperStarId B X))
    (Functor.mapDerivedCategoryNatIso (lowerStarId B X))
    (by simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd)
  rw [exact_right_adj (C := Sheaf X.smallEtaleTopology B)
    (D := Sheaf X.smallEtaleTopology B) (upperStarLowerStarAdjunction B (𝟙 X))] at he
  exact right_identity_conjugate _ _ _ _ he

end IdentityComparisons

private lemma composed_iso_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (R : C ⥤ D) (S : D ⥤ E) (T : C ⥤ E) (e : R ⋙ S ≅ T)
    {K : D} {L M : C} (a : K ⟶ R.obj L) (b : L ⟶ M) :
    S.map (a ≫ R.map b) ≫ e.hom.app M =
      S.map a ≫ e.hom.app L ≫ T.map b := by
  have hn := e.hom.naturality b
  dsimp only [Functor.comp_map] at hn
  rw [S.map_comp, Category.assoc, hn]

private lemma conjugate_iso_symm_eq
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₂ ≅ L₁) (r : R₁ ≅ R₂)
    (h : conjugateEquiv a b e.hom = r.hom) :
    (conjugateIsoEquiv a b).symm r = e := by
  apply (conjugateIsoEquiv a b).symm_apply_eq.mpr
  exact Iso.ext h.symm

section OpenCompositionComparisons

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryAdjunction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unbounded_sh_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j]
    (w : j₁ ≫ j₂ = j) :
    (unboundedFormalism A).shComp' j₁ j₂ j w =
      mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) w.symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) j₁ j₂ := by
  subst j
  rw [ExchangeFormalism.shComp', unbounded_pb_comp']
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr, Iso.refl_trans]
  apply conjugate_iso_symm_eq
  exact derived_open_comp_conjugate (ModuleCat.{u + 1} A) j₁ j₂

private lemma unbounded_pf_comp
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (unboundedFormalism A).pfComp' f g (f ≫ g) rfl =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).symm := by
  rw [ExchangeFormalism.pfComp', unbounded_pb_comp']
  rfl

private lemma exact_open_congr_symm
    (A : Type (u + 1)) [CommRing A] {U Z : Scheme.{u}} {j j' : U ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : j = j') :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm =
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).symm := by
  subst j'
  rfl

private lemma unbounded_comp_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) (K : DerivedCategoryModule A X) :
    ((unboundedFormalism A).compIso T).hom.app K =
      (lowerStar (ModuleCat.{u + 1} A) T.cg.g).rightDerivedFunctor.map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) T.isPullback).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cf.i).mapDerivedCategory.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} A) T.p).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
            (ModuleCat.{u + 1} A) T.cf.i T.q).inv.app K ≫
          (mapDerivedCategoryOpenImmersionLowerShriekCongr
            (ModuleCat.{u + 1} A) T.i_q).hom.app K)) ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} A) T.p)
        (lowerStar (ModuleCat.{u + 1} A) T.cg.g)
        (lowerStarComp (ModuleCat.{u + 1} A) T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cfg.i).mapDerivedCategory.obj K) := by
  rw [CompactSupportFormalism.compIso_hom_app,
    unbounded_open_exchange A T.isPullback, unbounded_sh_comp,
    exact_open_congr_symm,
    unbounded_pf_comp_inv A T.p T.cg.g T.cfg.g T.p_g]
  · simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    rfl

private lemma right_derived_star_comp_eq
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.rightDerivedFunctorCompIso'
      (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom := by
  have h := unbounded_pf_comp_inv A f g (f ≫ g) rfl
  rw [unbounded_pf_comp] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma unbounded_comp_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    (unboundedFormalism A).compIso (Compactification.Triangle.ofRestrict d e) =
      rightDerivedLowerShriekOfCompactificationCompIso A d e := by
  let B := ModuleCat.{u + 1} A
  have := isIso_openImmersionLowerShriekLowerStarExchange_of_isAddTorsion_ring A
    isAddTorsion_of_finite e.isPullback_restrict
  apply Iso.ext
  apply NatTrans.ext
  funext K
  change DerivedCategoryModule A X at K
  change (_ : ((rightDerivedLowerShriekOfCompactification B e.restrict ⋙
      rightDerivedLowerShriekOfCompactification B d).obj K ⟶
      (rightDerivedLowerShriekOfCompactification B (d.comp e)).obj K)) = _
  rw [unbounded_comp_hom_app]
  dsimp only [Compactification.Triangle.ofRestrict, Compactification.comp,
    Compactification.copy, Compactification.postcomp]
  erw [right_derived_star_comp_eq]
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  exact (composed_iso_naturality
    (lowerStar B e.g).rightDerivedFunctor (lowerStar B d.g).rightDerivedFunctor
    (lowerStar B (e.g ≫ d.g)).rightDerivedFunctor (rightDerivedLowerStarComp B e.g d.g)
    ((openImmersionLowerShriekLowerStarExchange B e.isPullback_restrict).app
      ((openImmersionLowerShriek B e.restrict.i).mapDerivedCategory.obj K))
    ((mapDerivedCategoryOpenImmersionLowerShriekComp B e.restrict.i
      (pullback.fst e.g d.i)).inv.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr B e.restrict_i_fst).hom.app K)).trans
      (Category.id_comp _).symm

end OpenCompositionComparisons

private lemma unbounded_base_change_refinement
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    ((unboundedFormalism A).baseChange (𝟙 X) c.i d.i r.hom hr.flip.w) =
      Functor.whiskerRight ((unboundedFormalism A).pbId X).hom
          ((unboundedFormalism A).sh c.i) ≫
        (Functor.leftUnitor _).hom ≫
          (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hr).hom := by
  let B := ModuleCat.{u + 1} A
  have key := mateEquiv_eq_of_unit ((unboundedFormalism A).shAdj d.i)
    ((unboundedFormalism A).shAdj c.i)
    (TwoSquare.mk ((unboundedFormalism A).pb (𝟙 X)) _ _ ((unboundedFormalism A).pb r.hom)
      (Functor.whiskerRight ((unboundedFormalism A).pbId X).hom
      ((unboundedFormalism A).sh c.i) ≫ (Functor.leftUnitor _).hom ≫
        (refinementLowerShriekBaseChangeDerivedIso B r hr).hom))
    ((unboundedFormalism A).sqIso (𝟙 X) c.i d.i r.hom hr.flip.w).hom (fun K ↦ ?_)
  · rw [ExchangeFormalism.baseChange, ← key]
    exact (Equiv.symm_apply_apply _ _)
  rw [ExchangeFormalism.sqIso_eq _ _ _ _ _ _ d.i (Category.id_comp _) r.i_hom]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.map_comp]
  rw [ExchangeFormalism.pbComp'_id_left_inv_app, unbounded_pb_comp']
  have h₁ := ((unboundedFormalism A).pbId X).hom.naturality
    (((unboundedFormalism A).shAdj d.i).unit.app K)
  have h₂ := ((unboundedFormalism A).shAdj c.i).unit_naturality
    ((exact_pb_id A X).hom.app K)
  have h₃ := unit_map_refinementLowerShriekBaseChangeDerivedIso B r hr K
  rw [upperStarCompIso_eq] at h₃
  erw [reassoc_of% h₁, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h₂]
  exact congrArg (fun t ↦ _ ≫ t) h₃.symm

private theorem unbounded_refinement_comparison
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (unboundedFormalism A).refinementComparison r hr =
      rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr := by
  rw [CompactSupportFormalism.refinementComparison_eq_of_baseChange
    (unboundedFormalism A) r hr
    (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hr)
    (unbounded_base_change_refinement A r hr), unbounded_pf_comp_inv,
    ← refinementLowerStarComp_eq]
  rfl

private theorem unbounded_shriek_iso
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f] (c d : Compactification f) :
    (unboundedFormalism A).shriekIso c d =
      rightDerivedLowerShriekOfCompactificationIso A c d := by
  ext : 1
  simp only [CompactSupportFormalism.shriekIso, rightDerivedLowerShriekOfCompactificationIso,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, unbounded_refinement_comparison]

private lemma unbounded_chosen_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)] :
    (unboundedFormalism A).lowerShriekCompIso f g =
      unboundedEtaleLowerShriekCompIso A f g := by
  rw [CompactSupportFormalism.lowerShriekCompIso]
  rw [← CompactSupportFormalism.shriekIso_symm]
  simp only [Compactification.Triangle.ofHasCompactification, unbounded_comp_iso,
    unbounded_shriek_iso, unboundedEtaleLowerShriekCompIso, rightDerivedLowerShriekIso]
  rfl

/-- The common-refinement comparisons satisfy the identity and cocycle laws. In particular,
passing through any third compactification produces the same map.
Source: Stacks Project, Tag 0F7I
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: identify the actual pairwise comparison with the compact-support formalism's
common-refinement comparison. Its identity and cocycle equations give both assertions;
the refinement-composition and naturality equations are already proved in that formalism. -/
theorem unboundedEtaleCompactSupport_comparison_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ c : Compactification f,
      rightDerivedLowerShriekOfCompactificationIso A c c = Iso.refl _) ∧
    (∀ c d e : Compactification f,
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
        rightDerivedLowerShriekOfCompactificationIso A d e =
          rightDerivedLowerShriekOfCompactificationIso A c e) := by
  constructor
  · intro c
    rw [← unbounded_shriek_iso]
    exact (unboundedFormalism A).shriekIso_refl c
  · intro c d e
    rw [← unbounded_shriek_iso, ← unbounded_shriek_iso, ← unbounded_shriek_iso]
    exact (unboundedFormalism A).shriekIso_trans c d e

end UnboundedFormalism

attribute [local instance] unbounded_has_base_change unbounded_has_proper_exchange

/-- The graph-normalized comparison for the coarser open of a proper refinement.
The two Noetherian structures on the ambient are consequences of properness over the
Noetherian target, supplied explicitly rather than added as hypotheses.
Source: Stacks Project, Tags 0F7I and 0F7B
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleRefinementOpenComparison
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (N : EtaleCompactSupportNormalization A) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i).mapDerivedCategory ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (refinementOpenCompactification r) :=
  letI : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  letI : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  (N.comparison d.i (refinementOpenCompactification r)).symm

/-- The composition isomorphism is computed by every proper/open tower. Thus it is
independent of compactification choices and commutes with their refinement comparisons.
Source: Stacks Project, Tag 0F7J
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: identify the formalism's triangle compositor with the actual proper/open tower
map, using the exact-derived open compositor and the canonical right-derived proper
compositor. Its every-triangle equation then gives the result for the supplied tower. -/
theorem unboundedEtaleLowerShriekCompIso_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    (unboundedEtaleLowerShriekCompIso A f g).hom =
      NatTrans.hcomp (rightDerivedLowerShriekIso A e.restrict).inv
        (rightDerivedLowerShriekIso A d).inv ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
      (rightDerivedLowerShriekIso A (d.comp e)).hom  := by
  let T := Compactification.Triangle.ofRestrict d e
  have h := (unboundedFormalism A).lowerShriekCompIso_hom_eq T
  rw [← (unboundedFormalism A).shriekIso_symm
    T.cf (HasCompactification.compactification f),
    ← (unboundedFormalism A).shriekIso_symm
      T.cg (HasCompactification.compactification g)] at h
  rw [unbounded_chosen_comp] at h
  dsimp only [T] at h
  rw [unbounded_comp_iso] at h
  simp only [unbounded_shriek_iso, Iso.symm_hom, Compactification.Triangle.ofRestrict] at h
  convert! h using 1

private lemma interchange_units
    {C : Type*} [Category C] (L R : C ⥤ C) (l : L ≅ 𝟭 C) (r : R ≅ 𝟭 C) :
    Functor.isoWhiskerRight l R ≪≫ Functor.leftUnitor R ≪≫ r =
      Functor.isoWhiskerLeft L r ≪≫ Functor.rightUnitor L ≪≫ l := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    ]
  change (_ : R.obj (L.obj K) ⟶ K) = _
  erw [Category.id_comp, Category.id_comp]
  exact r.hom.naturality (l.hom.app K)

private lemma unbounded_sh_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).shId X =
      Functor.mapDerivedCategoryNatIso
        (Adjunction.leftAdjointIdIso
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
          (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫ Functor.mapDerivedCategoryIdIso _ := by
  rw [ExchangeFormalism.shId]
  apply conjugate_iso_symm_eq
  exact derived_open_id_conjugate A X

private lemma unbounded_pf_id
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (unboundedFormalism A).pfId X =
      (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
  exact derived_star_id_conjugate A X

/-- Congruence of the chosen compact-support functors under equality of morphisms.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleLowerShriekCongr
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f' := by
  subst h
  exact Iso.refl _

/-- The identity compactification, followed by the exact identity sum-extension comparison.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleLowerShriekId
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) ≅
      𝟭 (DerivedCategoryModule A X) :=
  (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
    identityEtaleCompactSupportComparison A X ≪≫
    Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
        (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma unbounded_chosen_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (X : Scheme.{u}) [HasCompactification (𝟙 X)] :
    (unboundedFormalism A).lowerShriekId X = unboundedEtaleLowerShriekId A X := by
  rw [CompactSupportFormalism.lowerShriekId,
    ← (unboundedFormalism A).shriekIso_symm
      (Compactification.ofIsProper (𝟙 X)) (HasCompactification.compactification (𝟙 X)),
    unbounded_shriek_iso, CompactSupportFormalism.shriekOfIsProperIdIso,
    unbounded_sh_id, unbounded_pf_id]
  rw [interchange_units]
  exact congrArg (fun e ↦
    (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫ e)
    (identity_tail_eq A X)

private lemma unbounded_chosen_congr
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    (unboundedFormalism A).lowerShriekCongr h = unboundedEtaleLowerShriekCongr A h := by
  cases h
  rfl

/-- Associativity is equality of the two specified natural transformations.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: identify the chosen compositor, congruence maps and units with the existing
compact-support formalism. Its associativity equation, proved by refining the tower and
pasting the proper/open squares, transports to the specified natural transformations. -/
theorem unboundedEtaleLowerShriekCompIso_assoc
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] [IsNoetherian T]
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h) ≫
      (unboundedEtaleLowerShriekCompIso A (f ≫ g) h).hom ≫
      (unboundedEtaleLowerShriekCongr A (Category.assoc f g h)).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleLowerShriekCompIso A g h).hom ≫
      (unboundedEtaleLowerShriekCompIso A f (g ≫ h)).hom  := by
  have h' := (unboundedFormalism A).lowerShriekCompIso_assoc f g h
  simp only [unbounded_chosen_comp] at h'
  have hc : (unboundedFormalism A).lowerShriekCongr (Category.assoc f g h) =
      unboundedEtaleLowerShriekCongr A (Category.assoc f g h) := by
    generalize Category.assoc f g h = he
    cases he
    rfl
  rw [hc] at h'
  exact h'

/-- Both unit laws have the canonical identity-compactification normalization.
Source: Stacks Project, Tag 0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: identify the chosen composition and identity comparisons with the compact-support
formalism. The open and proper identity compositors have the specified derived-unit
normalizations. Transport its left and right unit equations across these identifications. -/
theorem unboundedEtaleLowerShriekCompIso_units
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification (𝟙 X)] [HasCompactification (𝟙 Y)]
    [HasCompactification (𝟙 X ≫ f)] [HasCompactification (f ≫ 𝟙 Y)] :
    ((unboundedEtaleLowerShriekCompIso A (𝟙 X) f).hom =
      Functor.whiskerRight (unboundedEtaleLowerShriekId A X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr A (Category.id_comp f).symm).hom) ∧
    ((unboundedEtaleLowerShriekCompIso A f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (unboundedEtaleLowerShriekId A Y).hom ≫
        (Functor.rightUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr A (Category.comp_id f).symm).hom) := by
  constructor
  · have h := (unboundedFormalism A).lowerShriekCompIso_id_left f
    simp only [unbounded_chosen_comp, unbounded_chosen_id, unbounded_chosen_congr] at h
    exact h
  · have h := (unboundedFormalism A).lowerShriekCompIso_id_right f
    simp only [unbounded_chosen_comp, unbounded_chosen_id, unbounded_chosen_congr] at h
    exact h

/-- The exact inverse-image composition is the sheaf comparison descended termwise.
Source: Stacks Project, Tags 0F7H and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleUpperStarCompIso
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The exact inverse-image identity is the sheaf identity descended termwise.
Source: Stacks Project, Tags 0F7H and 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleUpperStarIdIso
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} A) X) ≪≫
    Functor.mapDerivedCategoryIdIso _

private lemma upperStar_comp_id_unit
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X) (by simp)) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).hom ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
          (unboundedEtaleUpperStarIdIso A X).hom = 𝟙 _ := by
  rw [upperStarComp_id_left]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [reassoc_of% Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    unboundedEtaleUpperStarIdIso, Iso.trans_hom]
  simp only [Functor.mapDerivedCategoryNatIso_symm, Iso.inv_hom_id_app_assoc]
  have hr : (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).rightUnitor = Iso.refl _ := rfl
  rw [hr]
  have he : Functor.mapDerivedCategoryNatIso
      (Iso.refl ((upperStar (ModuleCat.{u + 1} A) (𝟙 X)) ⋙ 𝟭 _)) = Iso.refl _ := by
    apply Iso.ext
    exact Functor.mapDerivedCategoryNatIso_refl
  rw [he]
  erw [Category.id_comp]
  exact congr_app (Functor.mapDerivedCategoryCompIso_comp_id
    (upperStar (ModuleCat.{u + 1} A) (𝟙 X))) K

private lemma identity_exchange_of_pasting
    {D E : Type*} [Category D] [Category E]
    (F : D ⥤ E) (I : D ⥤ D) (J : E ⥤ E)
    (C : F ⋙ J ⟶ I ⋙ F) [IsIso C]
    (e : I ≅ 𝟭 D) (d : J ≅ 𝟭 E) (δ : I ≅ I ⋙ I) (ε : J ≅ J ⋙ J)
    (hδ : δ.hom ≫ Functor.whiskerLeft I e.hom = 𝟙 _)
    (hε : ε.hom ≫ Functor.whiskerLeft J d.hom = 𝟙 _)
    (hp : ∀ K, C.app K = ε.hom.app (F.obj K) ≫ J.map (C.app K) ≫
      C.app (I.obj K) ≫ F.map (δ.inv.app K)) :
    C ≫ Functor.whiskerRight e.hom F ≫ (Functor.leftUnitor F).hom =
      Functor.whiskerLeft F d.hom ≫ (Functor.rightUnitor F).hom := by
  have : J.Faithful := Functor.Faithful.of_iso d.symm
  ext K
  have hδ' : δ.inv.app K = I.map (e.hom.app K) := by
    have h := congr_app hδ K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at h
    have he : e.hom.app (I.obj K) = I.map (e.hom.app K) := by
      apply (cancel_mono (e.hom.app K)).1
      exact (e.hom.naturality (e.hom.app K)).symm
    rw [he] at h
    apply (cancel_epi (δ.hom.app K)).1
    exact (δ.hom_inv_id_app K).trans h.symm
  let c := C.app K ≫ F.map (e.hom.app K)
  have h := hp K
  rw [hδ'] at h
  have hn : J.map (F.map (e.hom.app K)) ≫ C.app K =
      C.app (I.obj K) ≫ F.map (I.map (e.hom.app K)) :=
    C.naturality (e.hom.app K)
  rw [← hn, ← Category.assoc (J.map _) (J.map _) _, ← J.map_comp] at h
  have hc : ε.hom.app (F.obj K) ≫ J.map c = 𝟙 _ := by
    apply (cancel_mono (C.app K)).1
    simpa only [c, Category.id_comp, Category.assoc] using h.symm
  have hd : ε.hom.app (F.obj K) ≫ J.map (d.hom.app (F.obj K)) = 𝟙 _ := by
    have hd := congr_app hε (F.obj K)
    have he : d.hom.app (J.obj (F.obj K)) = J.map (d.hom.app (F.obj K)) := by
      apply (cancel_mono (d.hom.app (F.obj K))).1
      exact (d.hom.naturality (d.hom.app (F.obj K))).symm
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app, he] using hd
  have hcd : c = d.hom.app (F.obj K) := by
    apply J.map_injective
    apply (cancel_epi (ε.hom.app (F.obj K))).1
    exact hc.trans hd.symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app]
  change C.app K ≫ F.map (e.hom.app K) ≫ 𝟙 _ =
    d.hom.app (F.obj K) ≫ 𝟙 _
  simpa only [Category.comp_id] using hcd

/-- The chosen-compactification exchange with exact inverse images. This extends the
existing `exactCompactSupportExchange` from the chosen fibre product to an arbitrary
specified cartesian square, using exactly the same canonical exact-functor transport.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleCompactSupportExchange
    (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback sq) :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A) sq c ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v').hom _

/-- The proper open-restriction map, followed by the inverse of the open unit. It is the
map called lambda in the tower normalization, formed from the specified exact-derived mate.
Source: Stacks Project, Tag 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons). -/
noncomputable def unboundedEtaleProperOpenRestriction
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] (sq : IsPullback k r p i)
    (K : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} A) i).mapDerivedCategory.obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) p).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj K)) ⟶
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj K :=
  (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj K) ≫
    (rightDerivedLowerStar (ModuleCat.{u + 1} A) r).map
      ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) k).unit).inv.app K)

/-- The tower interchange has adjunct inverse to the specified proper open-restriction
exchange. The equation specifies the inverse without choosing any unrelated isomorphism.
Source: Stacks Project, Tag 0F7B, case (b)
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: descend the open adjunction and its triangles termwise. Proper base
change makes lambda invertible, and the open unit is invertible. The two mate formulas
for the tower exchange transpose to lambda inverse by triangle identities and mate pasting.
This is equality of the actual maps, and does not use stalks to detect derived morphisms. -/
theorem unboundedEtaleCompactSupport_tower_adjunct
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (K : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv
        _ _ ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq.flip).app K) ≫
      unboundedEtaleProperOpenRestriction A sq K =
        𝟙 ((rightDerivedLowerStar (ModuleCat.{u + 1} A) r).obj K) := by
  let B := ModuleCat.{u + 1} A
  let e := mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq.flip
  let α := TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso B sq.toCommSq).hom
  have := isIso_openImmersionLowerShriekBaseChangeMap B sq.flip
  have hα (M : DerivedCategoryModule A W) :
      (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit.app
          ((upperStar B r).mapDerivedCategory.obj M) ≫
        (upperStar B k).mapDerivedCategory.map (e.hom.app M) =
      (upperStar B r).mapDerivedCategory.map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction B i).unit.app M) ≫
        α.app ((openImmersionLowerShriek B i).mapDerivedCategory.obj M) := by
    exact Adjunction.mapDerivedCategoryAdjunction_mate
      (openImmersionLowerShriekUpperStarAdjunction B i)
      (openImmersionLowerShriekUpperStarAdjunction B k)
      (squareUpperStarIso B sq.toCommSq)
      (asIso (openImmersionLowerShriekBaseChangeMap B sq.flip.toCommSq))
      (unit_map_openImmersionLowerShriekBaseChangeMap_app B sq.flip.toCommSq) M
  have h := inverse_mates_unit
    (mapDerivedUpperStarLowerStarAdjunction B r)
    (mapDerivedUpperStarLowerStarAdjunction B p)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction B k) e α hα K
  change _ ≫ ((mateEquiv (mapDerivedUpperStarLowerStarAdjunction B p)
      (mapDerivedUpperStarLowerStarAdjunction B r) α).app
        ((openImmersionLowerShriek B k).mapDerivedCategory.obj K) ≫
      (rightDerivedLowerStar B r).map
        ((asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).inv.app K)) = _
  dsimp only [openImmersionLowerShriekLowerStarExchange]
  rw [← Category.assoc]
  erw [h]
  dsimp only [rightDerivedLowerStar, Functor.comp_obj, Functor.comp_map, Functor.id_obj]
  rw [← Functor.map_comp]
  have hc : (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit.app K ≫
      (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).inv.app K = 𝟙 K :=
    (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit).hom_inv_id_app K
  rw [hc]
  exact CategoryTheory.Functor.map_id _ _

set_option backward.isDefEq.respectTransparency false in
/-- `AlgebraicGeometry.Etale.unboundedEtaleCompactSupport_exchange_normalization` without the
noetherianity and finiteness hypotheses, which its proof does not use. -/
private theorem exchange_normalization_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom := by
  ext K
  have h := congrArg (fun η ↦ η.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K))
    (exact_exchange_transport A (IsPullback.of_hasPullback c.g v).toCommSq)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [unboundedEtaleCompactSupportExchange,
    rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    derivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at h ⊢
  simp only [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.map_comp]
  rw [← h]
  simp only [Category.assoc]
  rw [((openImmersionLowerShriek (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq).i).mapDerivedCategory).map_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a compactification, exchange is exactly proper exchange followed by the inverse
of the degreewise open-extension comparison, with the displayed canonical associators.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: expand the exact-functor transport in the existing exchange definition.
The proper factor becomes the exact inverse-image adjunction mate of
definition-derived-base-change-map. The open factor is the degreewise inverse conjugate of the sheaf
exchange, hence the map of def-weil-pbc-etale-shriek-base-change-map. Triangle identities cancel the
exact-functor transport isomorphisms. Localization descends this equation on every complex. -/
theorem unboundedEtaleCompactSupport_exchange_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback v' f' f v) (c : Compactification f) :
    unboundedEtaleCompactSupportExchange A sq c =
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g v).toCommSq) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A)
          (c.isPullback_i_ofIsPullback sq)).inv
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) (c.ofIsPullback sq).g) ≫
      (Functor.associator _ _ _).hom :=
  exchange_normalization_general A sq c

section UnboundedBaseChange

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryNatIso

private lemma unbounded_shriek_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    (sq : IsPullback v' f' f v)
    (c : Compactification f) :
    ((unboundedFormalism A).shriekBaseChangeOfIsPullback sq c) =
      unboundedEtaleCompactSupportExchange A sq c := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) (c.isPullback_i_ofIsPullback sq)
  have hh : inv ((unboundedFormalism A).baseChange v' (c.ofIsPullback sq).i c.i
      (pullback.fst c.g v) (c.isPullback_i_ofIsPullback sq).w) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [unbounded_open_base_change]
    exact Iso.hom_inv_id _
  rw [exchange_normalization_general]
  dsimp only [CompactSupportFormalism.shriekBaseChangeOfIsPullback,
    CompactSupportFormalism.shriekBaseChange, ExchangeFormalism.shriekBaseChange,
    TwoSquare.hComp, TwoSquare.mk]
  rw [unbounded_pf_base_change, hh]
  rfl

private lemma unbounded_chosen_base_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    ((unboundedFormalism A).lowerShriekBaseChange sq) =
      unboundedEtaleCompactSupportBaseChange A sq := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  dsimp only [CompactSupportFormalism.lowerShriekBaseChange, TwoSquare.whiskerBottom]
  have hbc := unbounded_shriek_base_change A sq c
  change (unboundedFormalism A).shriekBaseChangeOfIsPullback sq c = _ at hbc
  rw [hbc, unbounded_shriek_iso]
  rw [unboundedEtaleCompactSupportExchange, unboundedEtaleCompactSupportBaseChange,
    rightDerivedLowerShriekBaseChangeMap]
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  apply congrArg (fun t ↦ _ ≫ _ ≫ t)
  exact (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory B v').hom.app K)

/-- Compact-support exchange is an isomorphism on every unbounded complex, independently
of compactification, with the specified exact proper exchange and inverse open factor.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: identify the canonical exact-derived proper mate and the degreewise open base-change
isomorphism with the two factors of the compact-support formalism. Proper base change makes
the first factor invertible for finite coefficients. The formalism's refinement naturality
and common-refinement cocycle identify the result for every supplied compactification. -/
theorem unboundedEtaleCompactSupport_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' f v) :
    IsIso (unboundedEtaleCompactSupportBaseChange A sq) ∧
    ∀ c : Compactification f,
      unboundedEtaleCompactSupportBaseChange A sq =
        Functor.whiskerRight (rightDerivedLowerShriekIso A c).inv
          (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≫
        unboundedEtaleCompactSupportExchange A sq c ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
          (rightDerivedLowerShriekIso A (c.ofIsPullback sq)).hom := by
  constructor
  · let c := HasCompactification.compactification f
    have := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring A
      isAddTorsion_of_finite (IsPullback.of_hasPullback c.g v)
    have := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c
    dsimp only [unboundedEtaleCompactSupportBaseChange, rightDerivedLowerShriekBaseChangeMap]
    infer_instance
  · intro c
    rw [← unbounded_chosen_base_change A sq]
    have h := 
      ((unboundedFormalism A).lowerShriekBaseChange_eq sq c)
    rw [← (unboundedFormalism A).shriekIso_symm c
      (HasCompactification.compactification f)] at h
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      unbounded_shriek_base_change, unbounded_shriek_iso, Iso.symm_hom,
      Category.assoc] at h
    convert! h using 1

end UnboundedBaseChange

section HorizontalPasting
universe v w
open TwoSquare
private noncomputable def pullbackRefinement
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    c'.Refinement (c.ofIsPullback sq) where
  hom := hp.isoPullback.hom
  i_hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
        Compactification.ofIsPullback_i_fst]
      exact hi.w.symm
    · simp only [Category.assoc, IsPullback.isoPullback_hom_snd,
        Compactification.ofIsPullback_i_snd]
      exact c'.comm.symm
  hom_g := hp.isoPullback_hom_snd

private lemma pullbackRefinement_cartesian
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (c : Compactification f) (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (hi : IsPullback g' c'.i c.i h) (hp : IsPullback h c'.g c.g g) :
    IsPullback c'.i (𝟙 X') (pullbackRefinement sq c c' h hi hp).hom
      (c.ofIsPullback sq).i := by
  have : IsIso (pullbackRefinement sq c c' h hi hp).hom := by
    change IsIso hp.isoPullback.hom
    infer_instance
  exact IsPullback.of_vert_isIso ⟨by
    rw [Category.id_comp, Compactification.Refinement.i_hom]⟩

private lemma shriekBaseChange_arbitrary
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [QuasiCompact f'] (c : Compactification f) (c' : Compactification f')
    (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h)
    (hp : IsPullback h c'.g c.g g) :
    (F.shriekBaseChange c c' h hi hp) =
      (F.shriekBaseChangeOfIsPullback sq c) ≫
        Functor.whiskerLeft (F.pb g') (F.shriekIso (c.ofIsPullback sq) c').hom := by
  let r := pullbackRefinement sq c c' h hi hp
  have hr := pullbackRefinement_cartesian sq c c' h hi hp
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i :=
    by
      rw [Compactification.Refinement.id_hom]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
  have he := F.shriekBaseChange_refinementComparison
    (Compactification.Refinement.id c) hid r hr h hi hp
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip (by
      change h ≫ 𝟙 c.Z = hp.isoPullback.hom ≫ pullback.fst c.g g
      rw [Category.comp_id, hp.isoPullback_hom_fst])
  rw [F.refinementComparison_eq_id _ hid rfl] at he
  have hh : Functor.whiskerRight (𝟙 (F.shriek c)) (F.pb g) = 𝟙 _ := by
    apply NatTrans.ext
    funext K
    exact (F.pb g).map_id _
  erw [hh, Category.id_comp] at he
  rw [← F.shriekIso_symm c' (c.ofIsPullback sq), F.shriekIso_eq_symm r hr]
  exact he

private lemma chosenBaseChange_arbitrary
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (c : Compactification f) (c' : Compactification f')
    (h : c'.Z ⟶ c.Z) (hi : IsPullback g' c'.i c.i h)
    (hp : IsPullback h c'.g c.g g) :
    F.lowerShriekBaseChange sq =
      ((F.shriekBaseChange c c' h hi hp).whiskerTop
        (F.shriekIso (HasCompactification.compactification f) c).hom).whiskerBottom
        (F.shriekIso c' (HasCompactification.compactification f')).hom := by
  rw [F.lowerShriekBaseChange_eq sq c]
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    shriekBaseChange_arbitrary F sq c c' h hi hp]
  rw [← F.shriekIso_trans (c.ofIsPullback sq) c'
    (HasCompactification.compactification f')]
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]

private lemma chosenBaseChange_paste_horiz
    (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {b : Y' ⟶ Y} {a : Y'' ⟶ Y'} {b' : X' ⟶ X} {a' : X'' ⟶ X'}
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback b' f' f b) (sq₂ : IsPullback a' f'' f' a)
    (sq₃ : IsPullback (a' ≫ b') f'' f (a ≫ b)) :
    F.lowerShriekBaseChange sq₃ =
      ((F.lowerShriekBaseChange sq₁ ≫ᵥ F.lowerShriekBaseChange sq₂).whiskerLeft
        (F.pbComp a' b').inv).whiskerRight (F.pbComp a b).hom := by
  let c := HasCompactification.compactification f
  let c' := c.ofIsPullback sq₁
  let c'' := c'.ofIsPullback sq₂
  let h₁ : c''.Z ⟶ c'.Z := pullback.fst c'.g a
  let h₂ : c'.Z ⟶ c.Z := pullback.fst c.g b
  have hi₁ := c'.isPullback_i_ofIsPullback sq₂
  have hp₁ := (c'.isPullback_g_ofIsPullback sq₂).flip
  have hi₂ := c.isPullback_i_ofIsPullback sq₁
  have hp₂ := (c.isPullback_g_ofIsPullback sq₁).flip
  have hi := hi₁.paste_horiz hi₂
  have hp := hp₁.paste_horiz hp₂
  rw [chosenBaseChange_arbitrary F sq₃ c c'' (h₁ ≫ h₂) hi hp,
    chosenBaseChange_arbitrary F sq₁ c c' h₂ hi₂ hp₂,
    chosenBaseChange_arbitrary F sq₂ c' c'' h₁ hi₁ hp₁,
    F.shriekBaseChange_paste_horiz c c' c'' h₁ h₂ hi₁ hp₁ hi₂ hp₂ hi hp]
  ext K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, ExchangeFormalism.pbComp'_rfl,
    Functor.comp_obj]
  have hc₀ : (F.shriekIso (HasCompactification.compactification f) c).hom.app K = 𝟙 _ :=
    congrArg (fun e ↦ e.hom.app K) (F.shriekIso_refl c)
  erw [hc₀]
  simp only [
     CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.map_comp, Category.assoc]
  rw [← F.shriekIso_symm c' (HasCompactification.compactification f')]
  have hc : (F.pb a).map
        ((F.shriekIso c' (HasCompactification.compactification f')).hom.app
          ((F.pb b').obj K)) ≫
      (F.pb a).map
        ((F.shriekIso c' (HasCompactification.compactification f')).inv.app
          ((F.pb b').obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  simp only [Iso.symm_hom]
  rw [reassoc_of% hc]
  erw [((F.shriekIso c''
    (HasCompactification.compactification f'')).hom.naturality
      ((F.pbComp a' b').inv.app K))]
  rfl

end HorizontalPasting

/-- **Horizontal pasting of the compact-support exchange maps**: the exchange map of two
successive changes of base `Y'' ⟶ Y' ⟶ Y` is the composite of the two exchange maps, up to the
termwise inverse-image composition isomorphisms. This is
`AlgebraicGeometry.Etale.unboundedEtaleCompactSupport_baseChange_comp` without its noetherianity
and finiteness hypotheses. -/
theorem unboundedEtaleCompactSupportBaseChange_paste_horiz
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') := by
  have h := 
    (chosenBaseChange_paste_horiz (unboundedFormalism A) sq₁ sq₂ sq₃)
  have hc {S T U : Scheme.{u}} (a : S ⟶ T) (b : T ⟶ U) :
      (unboundedFormalism A).pbComp a b = unboundedEtaleUpperStarCompIso A a b := rfl
  rw [hc, hc] at h
  simp only [unbounded_chosen_base_change, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.vComp] at h
  change (_ : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      (upperStar (ModuleCat.{u + 1} A) (w ≫ v)).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (w' ≫ v')).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'')) = _ at h
  simp only [Category.assoc] at h
  exact h

/-- Successive changes of base give the composite exchange, with the termwise
inverse-image composition identifications.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: use the twice base-changed compactification and the formalism's horizontal pasting
equation. Its refinement square identifies the transported maps with the specified chosen
exchanges; the common-refinement factors cancel by the comparison cocycle. -/
theorem unboundedEtaleCompactSupport_baseChange_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] [HasCompactification f'] [HasCompactification f'']
    [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback v' f' f v) (sq₂ : IsPullback w' f'' f' w)
    (sq₃ : IsPullback (w' ≫ v') f'' f (w ≫ v)) :
    unboundedEtaleCompactSupportBaseChange A sq₃ =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleUpperStarCompIso A w v).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sq₁)
        (upperStar (ModuleCat.{u + 1} A) w).mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory
        (unboundedEtaleCompactSupportBaseChange A sq₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleUpperStarCompIso A w' v').inv
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f'') :=
  unboundedEtaleCompactSupportBaseChange_paste_horiz A sq₁ sq₂ sq₃

attribute [local irreducible] unboundedEtaleCompactSupportBaseChange

set_option backward.isDefEq.respectTransparency true in
/-- Identity base changes give identity exchange after the canonical pullback unit maps.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: apply the horizontal pasting equation with an identity change of base. Cancel the
invertible compact-support exchange. Naturality of the inverse-image compositor and its
unit equation give precisely the displayed identity after the canonical unit maps. -/
theorem unboundedEtaleCompactSupport_baseChange_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (sq : IsPullback (𝟙 X) f f (𝟙 Y)) :
    unboundedEtaleCompactSupportBaseChange A sq ≫
        Functor.whiskerRight (unboundedEtaleUpperStarIdIso A X).hom _ ≫
        (Functor.leftUnitor _).hom =
      Functor.whiskerLeft _ (unboundedEtaleUpperStarIdIso A Y).hom ≫
        (Functor.rightUnitor _).hom := by
  let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
  let I := (upperStar (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
  let J := (upperStar (ModuleCat.{u + 1} A) (𝟙 Y)).mapDerivedCategory
  let C := unboundedEtaleCompactSupportBaseChange A sq
  have : IsIso C := (unboundedEtaleCompactSupport_baseChange A sq).1
  apply identity_exchange_of_pasting F I J C
    (unboundedEtaleUpperStarIdIso A X) (unboundedEtaleUpperStarIdIso A Y)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X) (by simp)) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) (𝟙 Y) (𝟙 Y) (𝟙 Y) (by simp)) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
    (exact_pb_id_left A (𝟙 X)) (exact_pb_id_left A (𝟙 Y))
  intro K
  have h := unboundedEtaleCompactSupport_baseChange_comp A sq sq
    (by simpa only [Category.id_comp] using sq)
  have hK := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    unboundedEtaleUpperStarCompIso] at hK
  dsimp only [F, I, J, C]
  exact hK

/-- **Vertical pasting of the compact-support exchange maps**: for two stacked cartesian squares
along `f` and `g`, the exchange map of the outer rectangle along `f ≫ g` is the composite of the
two exchange maps, up to the composition isomorphisms
`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso`. This is
`AlgebraicGeometry.Etale.unboundedEtaleCompactSupport_baseChange_composition` without its
noetherianity, separatedness and finiteness hypotheses. -/
theorem unboundedEtaleCompactSupportBaseChange_paste_vert
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ≫
      unboundedEtaleCompactSupportBaseChange A sqgf =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleCompactSupportBaseChange A sqg) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sqf)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory
        (unboundedEtaleLowerShriekCompIso A f' g').hom  := by
  have h₀ := 
    ((unboundedFormalism A).lowerShriekBaseChange_paste_vert sqf sqg sqgf)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    Category.assoc] at h₀
  have h := (Iso.eq_inv_comp (Functor.isoWhiskerRight
    ((unboundedFormalism A).lowerShriekCompIso f g)
    ((unboundedFormalism A).pb vZ))).mp h₀
  simp only [Functor.isoWhiskerRight_hom, unbounded_chosen_comp,
    unbounded_chosen_base_change, TwoSquare.hComp] at h
  change (_ : ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) ⋙
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f' ≫ g'))) = _ at h
  simp only [Category.assoc] at h
  exact h

/-- Base change is compatible with the specified compact-support composition maps.
Source: Stacks Project, Tag 0F7L
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: apply the proved compact-support-formalism exchange/compositor pasting equation.
Identify its chosen compact-support compositor and exchange with the concrete maps, and
its inverse-image compositor with the exact termwise-derived inverse-image comparison.
The resulting component equation is the asserted equality. -/
theorem unboundedEtaleCompactSupport_baseChange_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' Z Z' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    [IsNoetherian Z] [IsNoetherian Z']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ Z} {g' : Y' ⟶ Z'}
    {vX : X' ⟶ X} {vY : Y' ⟶ Y} {vZ : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [QuasiCompact f'] [QuasiCompact g'] [QuasiCompact (f' ≫ g')]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [HasCompactification f'] [HasCompactification g'] [HasCompactification (f' ≫ g')]
    (sqf : IsPullback vX f' f vY) (sqg : IsPullback vY g' g vZ)
    (sqgf : IsPullback vX (f' ≫ g') (f ≫ g) vZ) :
    Functor.whiskerRight (unboundedEtaleLowerShriekCompIso A f g).hom
        (upperStar (ModuleCat.{u + 1} A) vZ).mapDerivedCategory ≫
      unboundedEtaleCompactSupportBaseChange A sqgf =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
        (unboundedEtaleCompactSupportBaseChange A sqg) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (unboundedEtaleCompactSupportBaseChange A sqf)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) vX).mapDerivedCategory
        (unboundedEtaleLowerShriekCompIso A f' g').hom  :=
  unboundedEtaleCompactSupportBaseChange_paste_vert A sqf sqg sqgf

section BoundedBelowRestriction

open Abelian

private lemma right_derived_plus_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K) := by
  simpa only [Functor.rightDerivedFunctorPlusCompatibility, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] using
      (Functor.rightDerivedNatTrans_app
        (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
        F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
        (HomotopyCategory.Plus.quasiIso C) (𝟙 _) K)

private lemma right_derived_plus_unit_assoc
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [HasKInjectiveResolutions C] (F : C ⥤ D) [F.Additive]
    (K : HomotopyCategory.Plus C) {Z : DerivedCategory D}
    (h : F.rightDerivedFunctor.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.Plus.ι C).obj K)) ⟶ Z) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) ≫ h =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K) ≫ h := by
  rw [← Category.assoc, right_derived_plus_unit]

private lemma right_derived_natTrans_plus
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    [HasKInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatTrans τ) DerivedCategory.Plus.ι ≫
        G.rightDerivedFunctorPlusCompatibility.hom =
      F.rightDerivedFunctorPlusCompatibility.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedFunctorNatTrans τ) := by
  apply (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).rightDerived_ext
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightDerivedFunctorPlusιUnit]
  rw [← Functor.map_comp_assoc, Functor.rightDerivedFunctorPlusNatTrans_app,
    Functor.map_comp, Category.assoc, right_derived_plus_unit, right_derived_plus_unit_assoc]
  change DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app ((HomotopyCategory.Plus.ι C).obj K)) ≫
        G.rightDerivedFunctorUnit.app ((HomotopyCategory.Plus.ι C).obj K) = _
  exact (Functor.rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh)
    ((HomotopyCategory.Plus.ι C).obj K)).symm

private lemma right_comp_unit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (K : HomotopyCategory C (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app K ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit F G).app K := by
  simpa only [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    (Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
      (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) (F ⋙ G).rightDerivedFunctorUnit
      (Functor.rightDerivedFunctorCompUnit F G)
      (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) K)

private lemma right_derived_comp_plus
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes] :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso F G).hom
        DerivedCategory.Plus.ι ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F.rightDerivedFunctorPlus G.rightDerivedFunctorPlusCompatibility.hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight F.rightDerivedFunctorPlusCompatibility.hom G.rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom =
    (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedFunctorCompIso F G).hom := by
  apply ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).rightDerived_ext
    (F ⋙ G).rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
  apply NatTrans.ext
  funext K
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp_assoc, Functor.rightDerivedFunctorPlusCompIso_fac_app,
    Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
  have hn := G.rightDerivedFunctorPlusCompatibility.hom.naturality
    (F.rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, reassoc_of% hn]
  rw [right_derived_plus_unit_assoc, right_derived_plus_unit_assoc]
  have hl := (G.rightDerivedFunctor.map_comp
      (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app K))
      (F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K))).symm.trans
    (congrArg G.rightDerivedFunctor.map (right_derived_plus_unit F K))
  have hr := right_comp_unit F G ((HomotopyCategory.Plus.ι C).obj K)
  simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp, Category.comp_id] at hr
  let e := Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)
  let I := (HomotopyCategory.Plus.ι C).obj K
  have hh : e.hom.app I = 𝟙 _ :=
    Functor.mapHomotopyCategoryCompIso_refl_hom_app (.up ℤ) F G I
  have hi : e.inv.app I = 𝟙 _ :=
    (Category.comp_id _).symm.trans
      ((congrArg (fun m ↦ e.inv.app I ≫ m) hh.symm).trans (Iso.inv_hom_id_app e I))
  rw [hi, CategoryTheory.Functor.map_id, Category.id_comp] at hr
  exact (congrArg (fun t ↦ G.rightDerivedFunctorUnit.app
    ((HomotopyCategory.Plus.ι D).obj (F.mapHomotopyCategoryPlus.obj K)) ≫ t) hl).trans hr.symm

private lemma square_inverse {C : Type*} [Category C]
    {X Y X' Y' : C} (a : X ≅ Y) (b : X' ≅ Y')
    (kx : X ⟶ X') (ky : Y ⟶ Y') (h : a.hom ≫ ky = kx ≫ b.hom) :
    a.inv ≫ kx = ky ≫ b.inv := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, Iso.inv_hom_id_assoc]

private lemma right_derived_comp_prime_plus
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        ((Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app K) ≫
      H.rightDerivedFunctorPlusCompatibility.hom.app K =
    G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (Functor.rightDerivedFunctorCompIso' F G e).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  have ha := congr_app (right_derived_comp_plus F G) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at ha
  have hi := square_inverse
    (DerivedCategory.Plus.ι.mapIso ((Functor.rightDerivedFunctorPlusCompIso F G).app K))
    ((Functor.rightDerivedFunctorCompIso F G).app (DerivedCategory.Plus.ι.obj K))
    ((F ⋙ G).rightDerivedFunctorPlusCompatibility.hom.app K)
    (G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K))
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, Category.assoc] using ha)
  have hn := congr_app (right_derived_natTrans_plus e.hom) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn
  simp only [Functor.rightDerivedFunctorPlusCompIso',
    Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.rightDerivedFunctorPlusNatIso,
    Functor.rightDerivedFunctorNatIso, Functor.map_comp, Category.assoc]
  rw [hn]
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Category.assoc] using
    congrArg (fun t ↦ t ≫ (Functor.rightDerivedFunctorNatTrans e.hom).app
      (DerivedCategory.Plus.ι.obj K)) hi

section Proper
attribute [local irreducible] upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction Adjunction.mapDerivedCategoryPlusAdjunction

private lemma mate_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {R : D ⥤ C}
    {L' : E ⥤ F} {R' : F ⥤ E} (a : L ⊣ R) (b : L' ⊣ R')
    (α : G ⋙ L' ⟶ L ⋙ H) (K : D) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).app K =
      b.unit.app (G.obj (R.obj K)) ≫ R'.map (α.app (R.obj K)) ≫
        R'.map (H.map (a.counit.app K)) := by
  simp [mateEquiv_apply]

set_option backward.isDefEq.respectTransparency false in
private lemma exact_adjunction_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction B f).derivedPlus =
      Adjunction.restrictFullyFaithful
        (mapDerivedUpperStarLowerStarAdjunction B f)
        (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
        (upperStar B f).mapDerivedCategoryPlusCompatibility.symm
        (lowerStar B f).rightDerivedFunctorPlusCompatibility.symm := by
  have h := (upperStarLowerStarAdjunction B f
    ).derivedAdjunctionPlus_eq_derivedPlus
  dsimp only [Adjunction.derivedAdjunctionPlus] at h
  have he := mapDerivedUpperStarLowerStarAdjunction_eq B f
  dsimp only [derivedUpperStarLowerStarAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory] at he
  rewrite [← he] at h
  exact h.symm
attribute [local irreducible] upperStar lowerStar
private lemma exact_square_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map ((pullbackSquareComparison B sq).hom.app K) =
      (exactDerivedSquareUpperStarIso B sq).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  rewrite [pullbackSquareComparison_eq]
  have hc {T S : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ Y) (ab : T ⟶ Y)
      (hab : ab = a ≫ b) :
      DerivedCategory.Plus.ι.mapIso
          ((upperStarCompDerivedPlus B a b ab hab).app K) =
        (Functor.mapDerivedCategoryNatIso (upperStarComp B a b ab hab) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).app (DerivedCategory.Plus.ι.obj K) := by
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.app_hom, upperStarCompDerivedPlus,
      Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.symm_hom]
  change DerivedCategory.Plus.ι.map
      ((upperStarCompDerivedPlus B f' g (g' ≫ f) sq.w).inv.app K ≫
        (upperStarCompDerivedPlus B g' f).hom.app K) = _
  rewrite [Functor.map_comp]
  change (DerivedCategory.Plus.ι.mapIso
      ((upperStarCompDerivedPlus B f' g (g' ≫ f) sq.w).app K)).inv ≫
    (DerivedCategory.Plus.ι.mapIso
      ((upperStarCompDerivedPlus B g' f).app K)).hom = _
  rewrite [hc, hc]
  simp only [exactDerivedSquareUpperStarIso, squareUpperStarIso,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.app_inv, Iso.app_hom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Category.assoc]

section ProperExchangeRestriction
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.rightDerivedFunctorPlusCompatibility
private lemma exact_unit_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction B f).derivedPlus.unit.app K) =
      (mapDerivedUpperStarLowerStarAdjunction B f).unit.app
          (DerivedCategory.Plus.ι.obj K) ≫
        (lowerStar B f).rightDerivedFunctorPlusCompatibility.inv.app
          ((upperStar B f).mapDerivedCategoryPlus.obj K) := by
  have h := congrArg (fun adj ↦ DerivedCategory.Plus.ι.map (adj.unit.app K))
    (exact_adjunction_plus B f)
  simp only [Adjunction.map_restrictFullyFaithful_unit_app,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.symm_hom, Iso.refl_inv, NatTrans.id_app, ] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

private lemma exact_counit_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction B f).derivedPlus.counit.app K) =
      (upperStar B f).mapDerivedCategory.map
          ((lowerStar B f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (mapDerivedUpperStarLowerStarAdjunction B f).counit.app
          (DerivedCategory.Plus.ι.obj K) := by
  have h := congrArg (fun adj ↦ DerivedCategory.Plus.ι.map (adj.counit.app K))
    (exact_adjunction_plus B f)
  simp only [Adjunction.map_restrictFullyFaithful_counit_app,
    Functor.mapDerivedCategoryPlusCompatibility,
    Iso.symm_inv, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at h
  exact h

private lemma proper_exchange_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        ((derivedBaseChangeMapPlus B sq).app K) ≫
      (lowerStar B f').rightDerivedFunctorPlusCompatibility.hom.app
        ((upperStar B g').mapDerivedCategoryPlus.obj K) =
    (upperStar B g).mapDerivedCategory.map
        ((lowerStar B f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (exactDerivedBaseChangeMap B sq).app
        (DerivedCategory.Plus.ι.obj K) := by
  rw [← baseChange_eq_derivedBaseChangeMapPlus, baseChange_app_eq_mateEquiv]
  rewrite [mate_app (upperStarLowerStarAdjunction B f).derivedPlus
    (upperStarLowerStarAdjunction B f').derivedPlus]
  simp only [Functor.map_comp]
  let κ := (lowerStar B f').rightDerivedFunctorPlusCompatibility
  let α := (pullbackSquareComparison B sq).hom.app
    ((lowerStar B f).rightDerivedFunctorPlus.obj K)
  let ε := (upperStarLowerStarAdjunction B f).derivedPlus.counit.app K
  rewrite [exact_unit_plus B f'
    ((upperStar B g).mapDerivedCategoryPlus.obj
      ((lowerStar B f).rightDerivedFunctorPlus.obj K))]
  have hn := κ.hom.naturality
    ((upperStar B g').mapDerivedCategoryPlus.map ε)
  have hnα := κ.hom.naturality α
  simp only [Functor.comp_obj, Functor.comp_map] at hn hnα
  simp only [Category.assoc]
  erw [hn, reassoc_of% hnα]
  dsimp only [κ]
  erw [Iso.inv_hom_id_app_assoc]
  have hm : DerivedCategory.Plus.ι.map
      ((upperStar B g').mapDerivedCategoryPlus.map ε) =
      (upperStar B g').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ε) := rfl
  have hs := exact_square_plus B sq
    ((lowerStar B f).rightDerivedFunctorPlus.obj K)
  change DerivedCategory.Plus.ι.map α = _ at hs
  rewrite [hm, hs]
  dsimp only [ε]
  rewrite [exact_counit_plus B f K]
  simp only [Functor.map_comp]
  let k := (lowerStar B f).rightDerivedFunctorPlusCompatibility.hom.app K
  have hα := (exactDerivedSquareUpperStarIso B sq).hom.naturality k
  have hη := (mapDerivedUpperStarLowerStarAdjunction B f').unit.naturality
    ((upperStar B g).mapDerivedCategory.map k)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hα hη
  erw [← (lowerStar B f').rightDerivedFunctor.map_comp_assoc,
    ← hα, (lowerStar B f').rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hη]
  dsimp only [exactDerivedBaseChangeMap]
  rewrite [mate_app (mapDerivedUpperStarLowerStarAdjunction B f)
    (mapDerivedUpperStarLowerStarAdjunction B f')]
  rfl

end ProperExchangeRestriction
end Proper
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorPlusCompatibility
private lemma refinement_base_change_plus
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((refinementLowerShriekBaseChangeDerivedPlusIso (ModuleCat.{u + 1} A) r hp).inv.app K) =
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).inv.app
        (DerivedCategory.Plus.ι.obj K) := by
  have hh : DerivedCategory.Plus.ι.map
        ((refinementLowerShriekBaseChangeDerivedPlusIso (ModuleCat.{u + 1} A) r hp).hom.app K) =
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
    simp only [refinementLowerShriekBaseChangeDerivedPlusIso,
      refinementLowerShriekBaseChangeDerivedIso, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.symm_hom]
  have hi : DerivedCategory.Plus.ι.mapIso
      ((refinementLowerShriekBaseChangeDerivedPlusIso (ModuleCat.{u + 1} A) r hp).app K) =
      (refinementLowerShriekBaseChangeDerivedIso (ModuleCat.{u + 1} A) r hp).app
        (DerivedCategory.Plus.ι.obj K) := Iso.ext hh
  exact congrArg Iso.inv hi

private lemma refinement_comparison_plus
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hp : IsPullback c.i (𝟙 X) r.hom d.i)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusComparison
          (ModuleCat.{u + 1} A) r hp).app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) d).hom.app K ≫
      (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) r hp).app (DerivedCategory.Plus.ι.obj K) := by
  let B := ModuleCat.{u + 1} A
  let := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (upperStarLowerStarAdjunction B r.hom)
  let := (upperStarLowerStarAdjunction B r.hom).preservesKInjectiveComplexes
  have hc := right_derived_comp_prime_plus (lowerStar B r.hom) (lowerStar B d.g)
    (refinementLowerStarComp B r)
    ((openImmersionLowerShriek B c.i).mapDerivedCategoryPlus.obj K)
  have hu := exact_unit_plus (ModuleCat.{u + 1} A) r.hom
    ((openImmersionLowerShriek B d.i).mapDerivedCategoryPlus.obj K)
  have hb := refinement_base_change_plus A r hp K
  simp only [rightDerivedLowerShriekOfCompactificationPlusComparison,
    rightDerivedLowerShriekOfCompactificationComparison,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Iso.symm_hom, Iso.refl_hom, NatTrans.id_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [  Functor.comp_map]
  rw [reassoc_of% hc]
  have hn₁ := (lowerStar B d.g).rightDerivedFunctorPlusCompatibility.hom.naturality
    ((lowerStar B r.hom).rightDerivedFunctorPlus.map
      ((refinementLowerShriekBaseChangeDerivedPlusIso B r hp).inv.app K))
  have hn₂ := (lowerStar B d.g).rightDerivedFunctorPlusCompatibility.hom.naturality
    ((upperStarLowerStarAdjunction B r.hom).derivedPlus.unit.app
      ((openImmersionLowerShriek B d.i).mapDerivedCategoryPlus.obj K))
  simp only [Functor.comp_map] at hn₁ hn₂
  erw [reassoc_of% hn₁, reassoc_of% hn₂]
  erw [Category.comp_id, Category.id_comp]
  have hnq := (lowerStar B r.hom).rightDerivedFunctorPlusCompatibility.hom.naturality
    ((refinementLowerShriekBaseChangeDerivedPlusIso B r hp).inv.app K)
  simp only [Functor.comp_map] at hnq
  have ht : DerivedCategory.Plus.ι.map
        ((upperStarLowerStarAdjunction B r.hom).derivedPlus.unit.app
          ((openImmersionLowerShriek B d.i).mapDerivedCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.ι.map ((lowerStar B r.hom).rightDerivedFunctorPlus.map
        ((refinementLowerShriekBaseChangeDerivedPlusIso B r hp).inv.app K)) ≫
      (lowerStar B r.hom).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek B c.i).mapDerivedCategoryPlus.obj K) =
    (mapDerivedUpperStarLowerStarAdjunction B r.hom).unit.app
        (DerivedCategory.Plus.ι.obj
          ((openImmersionLowerShriek B d.i).mapDerivedCategoryPlus.obj K)) ≫
      (lowerStar B r.hom).rightDerivedFunctor.map
        ((refinementLowerShriekBaseChangeDerivedIso B r hp).inv.app
          (DerivedCategory.Plus.ι.obj K)) := by
    rw [hnq, hu]
    erw [Category.assoc, Iso.inv_hom_id_app_assoc, hb]
  have ht' := congrArg (lowerStar B d.g).rightDerivedFunctor.map ht
  simp only [Functor.map_comp] at ht'
  erw [reassoc_of% ht']
  rfl

/-- The pairwise comparisons restrict to the already specified bounded-below comparisons.
Source: Stacks Project, Tags 0F7H and 0F7I
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: compare the right-derived proper exchange and exact open adjunction under the
bounded-below inclusion, using their derived units, counits and square equations. This
identifies the cartesian refinement comparisons. Apply the two common-refinement factors
and their inverses to obtain equality of the specified pairwise comparison maps. -/
theorem unboundedEtaleCompactSupport_comparison_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f]
    (c d : Compactification f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) d).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app K ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
        (DerivedCategory.Plus.ι.obj K) := by
  let B := ModuleCat.{u + 1} A
  have hf := refinement_comparison_plus A (Compactification.infFst c d)
    (Compactification.isPullback_infFst c d) K
  have hs := refinement_comparison_plus A (Compactification.infSnd c d)
    (Compactification.isPullback_infSnd c d) K
  have hi := square_inverse
    (DerivedCategory.Plus.ι.mapIso ((asIso
      (rightDerivedLowerShriekOfCompactificationPlusComparison B
        (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).app K))
    ((asIso (rightDerivedLowerShriekOfCompactificationComparison B
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).app
        (DerivedCategory.Plus.ι.obj K))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B d).hom.app K)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B
      (Compactification.inf c d)).hom.app K)
    (by simpa only [Functor.mapIso_hom, Iso.app_hom, asIso_hom] using hs)
  simp only [Functor.mapIso_inv, Iso.app_inv, asIso_inv] at hi
  simp only [rightDerivedLowerShriekOfCompactificationPlusIso,
    rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, asIso_hom, asIso_inv, Functor.map_comp, Category.assoc]
  erw [hi, ← Category.assoc, hf, Category.assoc]

section ExchangeRestriction

private lemma mate_symm_app
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {R : D ⥤ C}
    {L' : E ⥤ F} {R' : F ⥤ E} (a : L ⊣ R) (b : L' ⊣ R')
    (α : R ⋙ G ⟶ H ⋙ R') (K : C) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ α)).app K =
      L'.map (G.map (a.unit.app K)) ≫ L'.map (α.app (L.obj K)) ≫
        b.counit.app (H.obj (L.obj K)) := by
  simp [mateEquiv]

private lemma exact_map_plus
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (t : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map t) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map t) := rfl

private lemma open_unit_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        ((openImmersionLowerShriekUpperStarAdjunction B j
          ).mapDerivedCategoryPlusAdjunction.unit.app K) =
      (openImmersionLowerShriekUpperStarAdjunction B j
        ).mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Plus.ι.obj K) := by
  dsimp only [Adjunction.mapDerivedCategoryPlusAdjunction]
  rewrite [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private lemma open_counit_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        ((openImmersionLowerShriekUpperStarAdjunction B j
          ).mapDerivedCategoryPlusAdjunction.counit.app K) =
      (openImmersionLowerShriekUpperStarAdjunction B j
        ).mapDerivedCategoryAdjunction.counit.app (DerivedCategory.Plus.ι.obj K) := by
  dsimp only [Adjunction.mapDerivedCategoryPlusAdjunction]
  rewrite [Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv, Iso.refl_hom,
    NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

private lemma exact_square_inv_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map ((pullbackSquareComparison B sq).inv.app K) =
      (exactDerivedSquareUpperStarIso B sq).inv.app
        (DerivedCategory.Plus.ι.obj K) := by
  have h : DerivedCategory.Plus.ι.mapIso
      ((pullbackSquareComparison B sq).app K) =
      (exactDerivedSquareUpperStarIso B sq).app
        (DerivedCategory.Plus.ι.obj K) := Iso.ext (exact_square_plus B sq K)
  exact congrArg Iso.inv h

private lemma open_exchange_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
      (((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction B r
          ).mapDerivedCategoryPlusAdjunction
        (openImmersionLowerShriekUpperStarAdjunction B l
          ).mapDerivedCategoryPlusAdjunction).symm
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison
            B sq.toCommSq).inv)).app K) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        B sq).hom.app (DerivedCategory.Plus.ι.obj K) := by
  rewrite [open_exchange_mate_coefficients]
  rewrite [mate_symm_app, mate_symm_app]
  simp only [Functor.map_comp, exact_map_plus, open_unit_plus, open_counit_plus,
    exact_square_inv_plus]
  rfl

private lemma plus_open_base_change_mate
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} (t : U' ⟶ U) (l : U' ⟶ Z')
    (r : U ⟶ Z) (b : Z' ⟶ Z) [IsOpenImmersion r] [IsOpenImmersion l]
    (w : t ≫ r = l ≫ b) :
    (derivedPlusFormalism B).baseChange t l r b w =
      ((mateEquiv
        (openImmersionLowerShriekUpperStarAdjunction B r
          ).mapDerivedCategoryPlusAdjunction
        (openImmersionLowerShriekUpperStarAdjunction B l
          ).mapDerivedCategoryPlusAdjunction).symm
        (TwoSquare.mk _ _ _ _
          (pullbackSquareComparison B (CommSq.mk w)).inv)) := by
  rw [ExchangeFormalism.baseChange, derivedPlusFormalism_sqIso]
  rfl

attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction
  Adjunction.mapDerivedCategoryPlusAdjunction upperStarLowerStarAdjunction
  mapDerivedUpperStarLowerStarAdjunction Adjunction.derivedPlus
  Adjunction.mapDerivedCategoryAdjunction
private lemma inverse_app_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (i : D ⥤ E) {F G : C ⥤ D} (β : F ⟶ G) [IsIso β]
    (K : C) (e : i.obj (F.obj K) ≅ i.obj (G.obj K))
    (h : i.map (β.app K) = e.hom) : i.map ((inv β).app K) = e.inv := by
  apply (cancel_epi e.hom).1
  rw [← h, ← i.map_comp, ← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app,
    i.map_id, h, e.hom_inv_id]

private theorem bounded_open_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b) :
    IsIso ((derivedPlusFormalism (ModuleCat.{u + 1} A)).baseChange t l r b sq.w) :=
  CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := derivedPlusFormalism (ModuleCat.{u + 1} A)) sq

private lemma plus_open_forward
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
      (((derivedPlusFormalism B).baseChange t l r b sq.w).app K) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        B sq).hom.app (DerivedCategory.Plus.ι.obj K) := by
  have hβ := (plus_open_base_change_mate B t l r b sq.w)
  change @Eq ((upperStar B t).mapDerivedCategoryPlus ⋙
      (openImmersionLowerShriek B l).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek B r).mapDerivedCategoryPlus ⋙
        (upperStar B b).mapDerivedCategoryPlus) _ _ at hβ
  have hsq : CommSq.mk sq.w = sq.toCommSq := Subsingleton.elim _ _
  rw [hsq] at hβ
  have hβK := congrArg
    (fun β : (upperStar B t).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek B l).mapDerivedCategoryPlus ⟶
        (openImmersionLowerShriek B r).mapDerivedCategoryPlus ⋙
          (upperStar B b).mapDerivedCategoryPlus ↦
      (DerivedCategory.Plus.ι : DerivedCategory.Plus (Sheaf Z'.smallEtaleTopology B) ⥤
        DerivedCategory (Sheaf Z'.smallEtaleTopology B)).map (β.app K)) hβ
  exact hβK.trans (open_exchange_plus B sq K)

private lemma plus_open_inverse
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    [IsIso ((derivedPlusFormalism B).baseChange t l r b sq.w)]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
      ((inv ((derivedPlusFormalism B).baseChange t l r b sq.w)
        ).app K) =
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        B sq).inv.app (DerivedCategory.Plus.ι.obj K) := by
  exact inverse_app_transport DerivedCategory.Plus.ι
    ((derivedPlusFormalism B).baseChange t l r b sq.w) K
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).app
      (DerivedCategory.Plus.ι.obj K)) (plus_open_forward B sq K)

private lemma proper_open_exchange_plus_generic
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    [IsIso ((derivedPlusFormalism B).baseChange t l r b sq.w)]
    (K : DerivedCategory.Plus (Sheaf U'.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        (((derivedPlusFormalism B).exchange t l r b sq.w).app K) ≫
      (lowerStar B b).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek B l).mapDerivedCategoryPlus.obj K) =
    (openImmersionLowerShriek B r).mapDerivedCategory.map
        ((lowerStar B t).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (openImmersionLowerShriekLowerStarExchange B sq).app
        (DerivedCategory.Plus.ι.obj K) := by
  let γ : (openImmersionLowerShriek B r).mapDerivedCategoryPlus ⋙
      (upperStar B b).mapDerivedCategoryPlus ⟶
      (upperStar B t).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek B l).mapDerivedCategoryPlus :=
    inv ((derivedPlusFormalism B).baseChange t l r b sq.w)
  change DerivedCategory.Plus.ι.map
      ((mateEquiv (upperStarLowerStarAdjunction B t).derivedPlus
        (upperStarLowerStarAdjunction B b).derivedPlus
        (TwoSquare.mk _ _ _ _ γ)).app K) ≫ _ = _
  rewrite [mate_app (upperStarLowerStarAdjunction B t).derivedPlus
    (upperStarLowerStarAdjunction B b).derivedPlus]
  simp only [Functor.map_comp]
  let κ := (lowerStar B b).rightDerivedFunctorPlusCompatibility
  let α := γ.app ((lowerStar B t).rightDerivedFunctorPlus.obj K)
  let ε := (upperStarLowerStarAdjunction B t).derivedPlus.counit.app K
  erw [exact_unit_plus B b
    ((openImmersionLowerShriek B r).mapDerivedCategoryPlus.obj
      ((lowerStar B t).rightDerivedFunctorPlus.obj K))]
  have hn := κ.hom.naturality
    ((openImmersionLowerShriek B l).mapDerivedCategoryPlus.map ε)
  have hnα := κ.hom.naturality α
  simp only [Functor.comp_obj, Functor.comp_map] at hn hnα
  simp only [Category.assoc]
  erw [hn, reassoc_of% hnα]
  dsimp only [κ]
  erw [Iso.inv_hom_id_app_assoc]
  have hm : DerivedCategory.Plus.ι.map
      ((openImmersionLowerShriek B l).mapDerivedCategoryPlus.map ε) =
      (openImmersionLowerShriek B l).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ε) := rfl
  have hs := plus_open_inverse B sq ((lowerStar B t).rightDerivedFunctorPlus.obj K)
  change DerivedCategory.Plus.ι.map α = _ at hs
  rewrite [hm, hs]
  dsimp only [ε]
  rewrite [exact_counit_plus B t K]
  simp only [Functor.map_comp]
  let k := (lowerStar B t).rightDerivedFunctorPlusCompatibility.hom.app K
  have hα := (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso B sq).inv.naturality k
  have hη := (mapDerivedUpperStarLowerStarAdjunction B b).unit.naturality
    ((openImmersionLowerShriek B r).mapDerivedCategory.map k)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_map] at hα hη
  erw [← (lowerStar B b).rightDerivedFunctor.map_comp_assoc,
    ← hα, (lowerStar B b).rightDerivedFunctor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hη]
  dsimp only [openImmersionLowerShriekLowerStarExchange]
  rewrite [mate_app (mapDerivedUpperStarLowerStarAdjunction B t)
    (mapDerivedUpperStarLowerStarAdjunction B b)]
  rfl

private lemma proper_open_exchange_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    (K : DerivedCategory.Plus (Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let := bounded_open_isIso A sq
    DerivedCategory.Plus.ι.map
        (((derivedPlusFormalism (ModuleCat.{u + 1} A)).exchange t l r b sq.w).app K) ≫
      (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) l).mapDerivedCategoryPlus.obj K) =
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) r).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) sq).app
        (DerivedCategory.Plus.ι.obj K) := by
  let := bounded_open_isIso A sq
  exact proper_open_exchange_plus_generic (ModuleCat.{u + 1} A) sq K

end ExchangeRestriction

section CompositionRestriction

-- Keep the sheaf adjunction abstract while comparing its derived units.
attribute [local irreducible] openImmersionLowerShriekUpperStarAdjunction

section BoundedOpenCompositor
attribute [local irreducible] Adjunction.mapDerivedCategoryPlusAdjunction
  upperStarLowerStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  Adjunction.derivedPlus Adjunction.mapDerivedCategoryAdjunction

private noncomputable def native_bounded_open_adj
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (openImmersionLowerShriek B j).mapDerivedCategoryPlus ⊣
      (upperStar B j).mapDerivedCategoryPlus :=
  (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryPlusAdjunction

private lemma bounded_open_comp_conjugate
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) [IsOpenImmersion j₁] [IsOpenImmersion j₂] :
    conjugateEquiv
      (C := DerivedCategory.Plus (Sheaf X.smallEtaleTopology B))
      (D := DerivedCategory.Plus (Sheaf Z.smallEtaleTopology B))
      (L₁ := (openImmersionLowerShriek B j₁).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek B j₂).mapDerivedCategoryPlus)
      (R₁ := (upperStar B j₂).mapDerivedCategoryPlus ⋙
        (upperStar B j₁).mapDerivedCategoryPlus)
      (L₂ := (openImmersionLowerShriek B (j₁ ≫ j₂)
        ).mapDerivedCategoryPlus)
      (R₂ := (upperStar B (j₁ ≫ j₂)).mapDerivedCategoryPlus)
      ((native_bounded_open_adj B j₁).comp
        (native_bounded_open_adj B j₂))
      (native_bounded_open_adj B (j₁ ≫ j₂))
      (Functor.mapDerivedCategoryPlusNatIso
        (openImmersionLowerShriekComp B j₁ j₂) ≪≫
          Functor.mapDerivedCategoryPlusCompIso
            (openImmersionLowerShriek B j₁)
            (openImmersionLowerShriek B j₂)).hom =
      (upperStarCompDerivedPlus B j₁ j₂).inv := by
  dsimp only [native_bounded_open_adj]
  apply conjugateEquiv_eq_of_unit
  intro K
  apply DerivedCategory.Plus.ι.map_injective
  have hd := unit_conjugateEquiv
    ((openImmersionLowerShriekUpperStarAdjunction B j₁
      ).mapDerivedCategoryAdjunction.comp
      (openImmersionLowerShriekUpperStarAdjunction B j₂
        ).mapDerivedCategoryAdjunction)
    (openImmersionLowerShriekUpperStarAdjunction B (j₁ ≫ j₂)
      ).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryTriangleIso
      (openImmersionLowerShriekComp B j₁ j₂)).hom
    (DerivedCategory.Plus.ι.obj K)
  conv at hd =>
    lhs
    rhs
    rw [derived_open_comp_conjugate B j₁ j₂]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, open_unit_plus,
    exact_map_plus, Iso.trans_hom, NatTrans.comp_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app]
  have hi (L : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology B)) :
      DerivedCategory.Plus.ι.map
        ((upperStarCompDerivedPlus B j₁ j₂).inv.app L) =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).inv.app
          (DerivedCategory.Plus.ι.obj L) := by
    have he : DerivedCategory.Plus.ι.mapIso
        ((upperStarCompDerivedPlus B j₁ j₂).app L) =
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp B j₁ j₂)).app
          (DerivedCategory.Plus.ι.obj L) := by
      apply Iso.ext
      simp only [Functor.mapIso_hom, Iso.app_hom, upperStarCompDerivedPlus,
        Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, NatTrans.comp_app,
        Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.symm_hom]
    exact congrArg Iso.inv he
  rw [hi]
  simp only [Adjunction.comp_unit_app, Functor.mapDerivedCategoryTriangleIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp] at hd
  convert! hd using 1
end BoundedOpenCompositor

private noncomputable def restriction_comp
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E]
    [Category Cp] [Category Dp] [Category Ep]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E}
    {F : C ⥤ D} {G : D ⥤ E} {Fp : Cp ⥤ Dp} {Gp : Dp ⥤ Ep}
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κG : Gp ⋙ iE ⟶ iD ⋙ G) :
    (Fp ⋙ Gp) ⋙ iE ⟶ iC ⋙ (F ⋙ G) :=
  (TwoSquare.hComp (TwoSquare.mk _ _ _ _ κF)
    (TwoSquare.mk _ _ _ _ κG))

private lemma restriction_comp_app
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E]
    [Category Cp] [Category Dp] [Category Ep]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E}
    {F : C ⥤ D} {G : D ⥤ E} {Fp : Cp ⥤ Dp} {Gp : Dp ⥤ Ep}
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κG : Gp ⋙ iE ⟶ iD ⋙ G) (K : Cp) :
    (restriction_comp κF κG).app K = κG.app (Fp.obj K) ≫ G.map (κF.app K) := by
  exact TwoSquare.hComp_app _ _ K

private lemma restriction_comp_assoc
    {C D E W Cp Dp Ep Wp : Type*}
    [Category C] [Category D] [Category E] [Category W]
    [Category Cp] [Category Dp] [Category Ep] [Category Wp]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E} {iW : Wp ⥤ W}
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ W}
    {Fp : Cp ⥤ Dp} {Gp : Dp ⥤ Ep} {Hp : Ep ⥤ Wp}
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κG : Gp ⋙ iE ⟶ iD ⋙ G)
    (κH : Hp ⋙ iW ⟶ iE ⋙ H) :
    restriction_comp (restriction_comp κF κG) κH =
      restriction_comp κF (restriction_comp κG κH) := by
  apply NatTrans.ext
  funext K
  simp only [restriction_comp_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, Category.assoc]

private lemma restriction_hcomp
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E]
    [Category Cp] [Category Dp] [Category Ep]
    (iC : Cp ⥤ C) (iD : Dp ⥤ D) (iE : Ep ⥤ E)
    (F F' : C ⥤ D) (G G' : D ⥤ E)
    (Fp Fp' : Cp ⥤ Dp) (Gp Gp' : Dp ⥤ Ep)
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κF' : Fp' ⋙ iD ⟶ iC ⋙ F')
    (κG : Gp ⋙ iE ⟶ iD ⋙ G) (κG' : Gp' ⋙ iE ⟶ iD ⋙ G')
    (α : F ⟶ F') (β : G ⟶ G') (αp : Fp ⟶ Fp') (βp : Gp ⟶ Gp')
    (hα : ∀ K, iD.map (αp.app K) ≫ κF'.app K = κF.app K ≫ α.app (iC.obj K))
    (hβ : ∀ K, iE.map (βp.app K) ≫ κG'.app K = κG.app K ≫ β.app (iD.obj K))
    (K : Cp) :
    iE.map ((NatTrans.hcomp αp βp).app K) ≫
      κG'.app (Fp'.obj K) ≫ G'.map (κF'.app K) =
    κG.app (Fp.obj K) ≫ G.map (κF.app K) ≫
      (NatTrans.hcomp α β).app (iC.obj K) := by
  simp only [NatTrans.hcomp_app, iE.map_comp, Category.assoc]
  have hn := κG'.naturality (αp.app K)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← G'.map_comp, hα, G'.map_comp]
  rw [reassoc_of% (hβ (Fp.obj K))]
  rw [← reassoc_of% (β.naturality (κF.app K))]

private lemma restriction_trans
    {C D Cp Dp : Type*} [Category C] [Category D] [Category Cp] [Category Dp]
    (iC : Cp ⥤ C) (iD : Dp ⥤ D)
    (F G H : C ⥤ D) (Fp Gp Hp : Cp ⥤ Dp)
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κG : Gp ⋙ iD ⟶ iC ⋙ G)
    (κH : Hp ⋙ iD ⟶ iC ⋙ H)
    (α : F ⟶ G) (β : G ⟶ H) (αp : Fp ⟶ Gp) (βp : Gp ⟶ Hp)
    (hα : ∀ K, iD.map (αp.app K) ≫ κG.app K = κF.app K ≫ α.app (iC.obj K))
    (hβ : ∀ K, iD.map (βp.app K) ≫ κH.app K = κG.app K ≫ β.app (iC.obj K))
    (K : Cp) :
    iD.map ((αp ≫ βp).app K) ≫ κH.app K =
      κF.app K ≫ (α ≫ β).app (iC.obj K) := by
  simp only [NatTrans.comp_app, iD.map_comp, Category.assoc]
  rw [hβ, ← Category.assoc, hα, Category.assoc]

private lemma restriction_hcomp_comp
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E]
    [Category Cp] [Category Dp] [Category Ep]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E}
    {F F' : C ⥤ D} {G G' : D ⥤ E}
    {Fp Fp' : Cp ⥤ Dp} {Gp Gp' : Dp ⥤ Ep}
    (κF : Fp ⋙ iD ⟶ iC ⋙ F) (κF' : Fp' ⋙ iD ⟶ iC ⋙ F')
    (κG : Gp ⋙ iE ⟶ iD ⋙ G) (κG' : Gp' ⋙ iE ⟶ iD ⋙ G')
    (α : F ⟶ F') (β : G ⟶ G') (αp : Fp ⟶ Fp') (βp : Gp ⟶ Gp')
    (hα : ∀ K, iD.map (αp.app K) ≫ κF'.app K = κF.app K ≫ α.app (iC.obj K))
    (hβ : ∀ K, iE.map (βp.app K) ≫ κG'.app K = κG.app K ≫ β.app (iD.obj K))
    (K : Cp) :
    iE.map ((NatTrans.hcomp αp βp).app K) ≫
      (restriction_comp κF' κG').app K =
    (restriction_comp κF κG).app K ≫
      (NatTrans.hcomp α β).app (iC.obj K) := by
  simpa only [restriction_comp_app, Category.assoc] using
    restriction_hcomp iC iD iE F F' G G' Fp Fp' Gp Gp' κF κF' κG κG'
      α β αp βp hα hβ K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma restriction_triangle
    {C D Y E Z W Cp Dp Yp Ep Zp Wp : Type*}
    [Category C] [Category D] [Category Y] [Category E] [Category Z] [Category W]
    [Category Cp] [Category Dp] [Category Yp] [Category Ep] [Category Zp] [Category Wp]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iY : Yp ⥤ Y}
    {iE : Ep ⥤ E} {iZ : Zp ⥤ Z} {iW : Wp ⥤ W}
    {O : C ⥤ D} {R : D ⥤ Y} {J : Y ⥤ E} {S : E ⥤ W}
    {Q : D ⥤ Z} {P : Z ⥤ E} {L : C ⥤ Z} {T : Z ⥤ W}
    {Op : Cp ⥤ Dp} {Rp : Dp ⥤ Yp} {Jp : Yp ⥤ Ep} {Sp : Ep ⥤ Wp}
    {Qp : Dp ⥤ Zp} {Pp : Zp ⥤ Ep} {Lp : Cp ⥤ Zp} {Tp : Zp ⥤ Wp}
    (κO : Op ⋙ iD ⟶ iC ⋙ O) (κR : Rp ⋙ iY ⟶ iD ⋙ R)
    (κJ : Jp ⋙ iE ⟶ iY ⋙ J) (κS : Sp ⋙ iW ⟶ iE ⋙ S)
    (κQ : Qp ⋙ iZ ⟶ iD ⋙ Q) (κP : Pp ⋙ iE ⟶ iZ ⋙ P)
    (κL : Lp ⋙ iZ ⟶ iC ⋙ L) (κT : Tp ⋙ iW ⟶ iZ ⋙ T)
    (ex : R ⋙ J ⟶ Q ⋙ P) (μ : O ⋙ Q ⟶ L) (ν : P ⋙ S ⟶ T)
    (exp : Rp ⋙ Jp ⟶ Qp ⋙ Pp) (μp : Op ⋙ Qp ⟶ Lp) (νp : Pp ⋙ Sp ⟶ Tp)
    (hex : ∀ K, iE.map (exp.app K) ≫ (restriction_comp κQ κP).app K =
      (restriction_comp κR κJ).app K ≫ ex.app (iD.obj K))
    (hμ : ∀ K, iZ.map (μp.app K) ≫ κL.app K =
      (restriction_comp κO κQ).app K ≫ μ.app (iC.obj K))
    (hν : ∀ K, iW.map (νp.app K) ≫ κT.app K =
      (restriction_comp κP κS).app K ≫ ν.app (iZ.obj K))
    (K : Cp) :
    iW.map (Sp.map (exp.app (Op.obj K) ≫ Pp.map (μp.app K)) ≫
        νp.app (Lp.obj K)) ≫
      (restriction_comp κL κT).app K =
    (restriction_comp (restriction_comp κO κR) (restriction_comp κJ κS)).app K ≫
      S.map (ex.app (O.obj (iC.obj K)) ≫ P.map (μ.app (iC.obj K))) ≫
        ν.app (L.obj (iC.obj K)) := by
  have h₁a := restriction_hcomp_comp
    (restriction_comp κR κJ) (restriction_comp κQ κP) κS κS
    ex (𝟙 S) exp (𝟙 Sp) hex (fun M ↦ by
      simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id])
  have h₁ := restriction_hcomp_comp κO κO
    (restriction_comp (restriction_comp κR κJ) κS)
    (restriction_comp (restriction_comp κQ κP) κS)
    (𝟙 O) (NatTrans.hcomp ex (𝟙 S)) (𝟙 Op) (NatTrans.hcomp exp (𝟙 Sp))
    (fun M ↦ by
      simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id]) h₁a
  have h₂ := restriction_hcomp_comp (restriction_comp κO κQ) κL
    (restriction_comp κP κS) (restriction_comp κP κS)
    μ (𝟙 (P ⋙ S)) μp (𝟙 (Pp ⋙ Sp)) hμ (fun M ↦ by
      simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id])
  have h₃ := restriction_hcomp_comp κL κL
    (restriction_comp κP κS) κT (𝟙 L) ν (𝟙 Lp) νp (fun M ↦ by
      simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [Category.comp_id]) hν
  simp only [restriction_comp_assoc] at h₁ h₂
  have h₁K := h₁ K
  have h₂K := h₂ K
  have h₃K := h₃ K
  simp only [restriction_comp_app, NatTrans.hcomp_app, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Functor.comp_map,
    Functor.comp_obj, Functor.map_comp, Category.assoc] at h₁K h₂K h₃K ⊢
  rw [h₃K, reassoc_of% h₂K, reassoc_of% h₁K]

private lemma restriction_triangle_transport
    {C D Y E Z W Cp Dp Yp Ep Zp Wp : Type*}
    [Category C] [Category D] [Category Y] [Category E] [Category Z] [Category W]
    [Category Cp] [Category Dp] [Category Yp] [Category Ep] [Category Zp] [Category Wp]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iY : Yp ⥤ Y}
    {iE : Ep ⥤ E} {iZ : Zp ⥤ Z} {iW : Wp ⥤ W}
    {O : C ⥤ D} {R : D ⥤ Y} {J : Y ⥤ E} {S : E ⥤ W}
    {Q : D ⥤ Z} {P : Z ⥤ E} {L : C ⥤ Z} {T : Z ⥤ W}
    {Op : Cp ⥤ Dp} {Rp : Dp ⥤ Yp} {Jp : Yp ⥤ Ep} {Sp : Ep ⥤ Wp}
    {Qp : Dp ⥤ Zp} {Pp : Zp ⥤ Ep} {Lp : Cp ⥤ Zp} {Tp : Zp ⥤ Wp}
    (κO : Op ⋙ iD ⟶ iC ⋙ O) (κR : Rp ⋙ iY ⟶ iD ⋙ R)
    (κJ : Jp ⋙ iE ⟶ iY ⋙ J) (κS : Sp ⋙ iW ⟶ iE ⋙ S)
    (κQ : Qp ⋙ iZ ⟶ iD ⋙ Q) (κP : Pp ⋙ iE ⟶ iZ ⋙ P)
    (κL : Lp ⋙ iZ ⟶ iC ⋙ L) (κT : Tp ⋙ iW ⟶ iZ ⋙ T)
    (ex : R ⋙ J ⟶ Q ⋙ P) (μ : O ⋙ Q ⟶ L) (ν : P ⋙ S ⟶ T)
    (exp : Rp ⋙ Jp ⟶ Qp ⋙ Pp) (μp : Op ⋙ Qp ⟶ Lp) (νp : Pp ⋙ Sp ⟶ Tp)
    (hex : ∀ K, iE.map (exp.app K) ≫ (restriction_comp κQ κP).app K =
      (restriction_comp κR κJ).app K ≫ ex.app (iD.obj K))
    (hμ : ∀ K, iZ.map (μp.app K) ≫ κL.app K =
      (restriction_comp κO κQ).app K ≫ μ.app (iC.obj K))
    (hν : ∀ K, iW.map (νp.app K) ≫ κT.app K =
      (restriction_comp κP κS).app K ≫ ν.app (iZ.obj K))
    (κOR : (Op ⋙ Rp) ⋙ iY ⟶ iC ⋙ (O ⋙ R))
    (κJS : (Jp ⋙ Sp) ⋙ iW ⟶ iY ⋙ (J ⋙ S))
    (κLT : (Lp ⋙ Tp) ⋙ iW ⟶ iC ⋙ (L ⋙ T))
    (hOR : κOR = restriction_comp κO κR)
    (hJS : κJS = restriction_comp κJ κS)
    (hLT : κLT = restriction_comp κL κT)
    (τ : (O ⋙ R) ⋙ (J ⋙ S) ⟶ L ⋙ T)
    (τp : (Op ⋙ Rp) ⋙ (Jp ⋙ Sp) ⟶ Lp ⋙ Tp)
    (hτ : ∀ K, τ.app K = S.map (ex.app (O.obj K) ≫ P.map (μ.app K)) ≫ ν.app (L.obj K))
    (hτp : ∀ K, τp.app K = Sp.map (exp.app (Op.obj K) ≫ Pp.map (μp.app K)) ≫ νp.app (Lp.obj K))
    (K : Cp) :
    iW.map (τp.app K) ≫ κLT.app K =
      κJS.app ((Op ⋙ Rp).obj K) ≫ (J ⋙ S).map (κOR.app K) ≫ τ.app (iC.obj K) := by
  rw [hOR, hJS, hLT, hτp, hτ]
  have h := restriction_triangle κO κR κJ κS κQ κP κL κT ex μ ν exp μp νp hex hμ hν K
  simpa only [restriction_comp_app, Category.assoc] using h

private lemma restriction_comp_iso_paste
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E]
    [Category Cp] [Category Dp] [Category Ep]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E}
    {F : C ⥤ D} {G : D ⥤ E} {Fp : Cp ⥤ Dp} {Gp : Dp ⥤ Ep}
    (κF : Fp ⋙ iD ≅ iC ⋙ F) (κG : Gp ⋙ iE ≅ iD ⋙ G) :
    restriction_comp κF.hom κG.hom =
      (Functor.associator Fp Gp iE ≪≫ Functor.isoWhiskerLeft Fp κG ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight κF G ≪≫
          Functor.associator _ _ _).hom := by
  apply NatTrans.ext
  funext K
  simp only [restriction_comp_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private lemma candidate_compat_nt
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B c).hom =
      restriction_comp
        (openImmersionLowerShriek B c.i).mapDerivedCategoryPlusCompatibility.hom
        (lowerStar B c.g).rightDerivedFunctorPlusCompatibility.hom := by
  exact (restriction_comp_iso_paste _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma full_exact_exchange
    {D Y Z E : Type*} [Category D] [Category Y] [Category Z] [Category E]
    [Abelian D] [Abelian Y] [Abelian Z] [Abelian E]
    [HasDerivedCategory D] [HasDerivedCategory Y]
    [HasDerivedCategory Z] [HasDerivedCategory E]
    [EnoughInjectives D] [EnoughInjectives Z]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions Z]
    (R : D ⥤ Y) (J : Y ⥤ E) (Q : D ⥤ Z) (P : Z ⥤ E)
    [R.Additive] [J.Additive] [Q.Additive] [P.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (ex : R.rightDerivedFunctor ⋙ J.mapDerivedCategory ⟶
      Q.mapDerivedCategory ⋙ P.rightDerivedFunctor)
    (exp : R.rightDerivedFunctorPlus ⋙ J.mapDerivedCategoryPlus ⟶
      Q.mapDerivedCategoryPlus ⋙ P.rightDerivedFunctorPlus)
    (h : ∀ K, DerivedCategory.Plus.ι.map (exp.app K) ≫
      P.rightDerivedFunctorPlusCompatibility.hom.app (Q.mapDerivedCategoryPlus.obj K) =
      J.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        ex.app (DerivedCategory.Plus.ι.obj K))
    (K : DerivedCategory.Plus D) :
    DerivedCategory.Plus.ι.map (exp.app K) ≫
      (restriction_comp Q.mapDerivedCategoryPlusCompatibility.hom
        P.rightDerivedFunctorPlusCompatibility.hom).app K =
      (restriction_comp R.rightDerivedFunctorPlusCompatibility.hom
        J.mapDerivedCategoryPlusCompatibility.hom).app K ≫
          ex.app (DerivedCategory.Plus.ι.obj K) := by
  simp only [restriction_comp_app, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  erw [P.rightDerivedFunctor.map_id, Category.comp_id]
  exact h K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma full_exact_composition
    {C D Z : Type*} [Category C] [Category D] [Category Z]
    [Abelian C] [Abelian D] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory Z]
    (O : C ⥤ D) (Q : D ⥤ Z) (L : C ⥤ Z)
    [O.Additive] [Q.Additive] [L.Additive]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (μ : O.mapDerivedCategory ⋙ Q.mapDerivedCategory ⟶ L.mapDerivedCategory)
    (μp : O.mapDerivedCategoryPlus ⋙ Q.mapDerivedCategoryPlus ⟶ L.mapDerivedCategoryPlus)
    (h : ∀ K, DerivedCategory.Plus.ι.map (μp.app K) =
      μ.app (DerivedCategory.Plus.ι.obj K))
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map (μp.app K) ≫ L.mapDerivedCategoryPlusCompatibility.hom.app K =
      (restriction_comp O.mapDerivedCategoryPlusCompatibility.hom
        Q.mapDerivedCategoryPlusCompatibility.hom).app K ≫
          μ.app (DerivedCategory.Plus.ι.obj K) := by
  simp only [restriction_comp_app, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  erw [Category.comp_id, Q.mapDerivedCategory.map_id, Category.id_comp]
  exact h K

private lemma full_proper_composition
    {Z E W : Type*} [Category Z] [Category E] [Category W]
    [Abelian Z] [Abelian E] [Abelian W]
    [HasDerivedCategory Z] [HasDerivedCategory E] [HasDerivedCategory W]
    [EnoughInjectives Z] [EnoughInjectives E]
    [Abelian.HasKInjectiveResolutions Z] [Abelian.HasKInjectiveResolutions E]
    (P : Z ⥤ E) (S : E ⥤ W) (T : Z ⥤ W)
    [P.Additive] [S.Additive] [T.Additive]
    (ν : P.rightDerivedFunctor ⋙ S.rightDerivedFunctor ⟶ T.rightDerivedFunctor)
    (νp : P.rightDerivedFunctorPlus ⋙ S.rightDerivedFunctorPlus ⟶ T.rightDerivedFunctorPlus)
    (h : ∀ K, DerivedCategory.Plus.ι.map (νp.app K) ≫
      T.rightDerivedFunctorPlusCompatibility.hom.app K =
        S.rightDerivedFunctorPlusCompatibility.hom.app (P.rightDerivedFunctorPlus.obj K) ≫
          S.rightDerivedFunctor.map (P.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
            ν.app (DerivedCategory.Plus.ι.obj K))
    (K : DerivedCategory.Plus Z) :
    DerivedCategory.Plus.ι.map (νp.app K) ≫ T.rightDerivedFunctorPlusCompatibility.hom.app K =
      (restriction_comp P.rightDerivedFunctorPlusCompatibility.hom
        S.rightDerivedFunctorPlusCompatibility.hom).app K ≫
          ν.app (DerivedCategory.Plus.ι.obj K) := by
  simpa only [restriction_comp_app, Category.assoc] using h K

private noncomputable def unbounded_sh_comp_map
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j]
    (w : j₁ ≫ j₂ = j) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j₁).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j₂).mapDerivedCategory ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  ((unboundedFormalism A).shComp' j₁ j₂ j w).inv

private noncomputable def native_unbounded_triangle_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cf ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cfg :=
  (unboundedFormalism A).compIso T

private lemma unbounded_tower_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (native_unbounded_triangle_iso A T).hom.app K =
      (lowerStar (ModuleCat.{u + 1} A) T.cg.g).rightDerivedFunctor.map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) T.isPullback).app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cf.i).mapDerivedCategory.obj K) ≫
          (lowerStar (ModuleCat.{u + 1} A) T.p).rightDerivedFunctor.map
            ((unbounded_sh_comp_map A T.cf.i T.q T.cfg.i T.i_q).app K)) ≫
        (Functor.rightDerivedFunctorCompIso' (lowerStar (ModuleCat.{u + 1} A) T.p)
          (lowerStar (ModuleCat.{u + 1} A) T.cg.g)
          (lowerStarComp (ModuleCat.{u + 1} A) T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) T.cfg.i
              ).mapDerivedCategory.obj K) := by
  unfold native_unbounded_triangle_iso
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := unboundedFormalism A) T.isPullback
  rw [CompactSupportFormalism.compIso_hom_app (unboundedFormalism A) T K,
    unbounded_pf_comp_inv]
  conv_lhs =>
    arg 1
    arg 2
    arg 1
    rw [unbounded_open_exchange A T.isPullback]
  rfl

private noncomputable def native_bounded_sh_comp
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}} (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j]
    (w : j₁ ≫ j₂ = j) :
    (openImmersionLowerShriek B j₁).mapDerivedCategoryPlus ⋙
      (openImmersionLowerShriek B j₂).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek B j).mapDerivedCategoryPlus :=
  ((derivedPlusFormalism B).shComp' j₁ j₂ j w).inv

private noncomputable def native_bounded_exchange
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {U U' Z Z' : Scheme.{u}} {t : U' ⟶ U} {l : U' ⟶ Z'}
    {r : U ⟶ Z} {b : Z' ⟶ Z} [IsOpenImmersion r] [IsOpenImmersion l]
    (sq : IsPullback t l r b)
    [IsIso ((derivedPlusFormalism B).baseChange t l r b sq.w)] :
    (lowerStar B t).rightDerivedFunctorPlus ⋙
      (openImmersionLowerShriek B r).mapDerivedCategoryPlus ⟶
      (openImmersionLowerShriek B l).mapDerivedCategoryPlus ⋙
        (lowerStar B b).rightDerivedFunctorPlus :=
  ((derivedPlusFormalism B).exchange t l r b sq.w)

private noncomputable def native_bounded_triangle_iso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [(derivedPlusFormalism B).HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    rightDerivedLowerShriekOfCompactificationPlus B T.cf ⋙
      rightDerivedLowerShriekOfCompactificationPlus B T.cg ≅
      rightDerivedLowerShriekOfCompactificationPlus B T.cfg :=
  (derivedPlusFormalism B).compIso T

private lemma bounded_sh_comp_plus
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (j₁ : X ⟶ Y) (j₂ : Y ⟶ Z) (j : X ⟶ Z)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j]
    (w : j₁ ≫ j₂ = j)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
      ((native_bounded_sh_comp (ModuleCat.{u + 1} A) j₁ j₂ j w).app K) =
      (unbounded_sh_comp_map A j₁ j₂ j w).app
        (DerivedCategory.Plus.ι.obj K) := by
  subst j
  let B := ModuleCat.{u + 1} A
  have hb : (derivedPlusFormalism B).shComp' j₁ j₂ (j₁ ≫ j₂) rfl =
      Functor.mapDerivedCategoryPlusNatIso (openImmersionLowerShriekComp B j₁ j₂) ≪≫
        Functor.mapDerivedCategoryPlusCompIso
          (openImmersionLowerShriek B j₁) (openImmersionLowerShriek B j₂) := by
    rw [ExchangeFormalism.shComp', derivedPlusFormalism_pbComp']
    apply conjugate_iso_symm_eq
    exact bounded_open_comp_conjugate B j₁ j₂
  have he : DerivedCategory.Plus.ι.mapIso
      (((derivedPlusFormalism B).shComp' j₁ j₂ (j₁ ≫ j₂) rfl).app K) =
    ((unboundedFormalism A).shComp' j₁ j₂ (j₁ ≫ j₂) rfl).app
      (DerivedCategory.Plus.ι.obj K) := by
    apply Iso.ext
    rw [hb, unbounded_sh_comp]
    simp only [Functor.mapIso_hom, Iso.app_hom, mapDerivedCategoryOpenImmersionLowerShriekCongr,
      Iso.refl_trans, mapDerivedCategoryOpenImmersionLowerShriekComp,
      Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.symm_hom]
    rfl
  exact congrArg Iso.inv he

private lemma bounded_tower_app_generic
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [(derivedPlusFormalism B).HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
      (F := derivedPlusFormalism B) T.isPullback
    (native_bounded_triangle_iso B T).hom.app K =
      (lowerStar B T.cg.g).rightDerivedFunctorPlus.map
        ((native_bounded_exchange B T.isPullback).app
            ((openImmersionLowerShriek B T.cf.i).mapDerivedCategoryPlus.obj K) ≫
          (lowerStar B T.p).rightDerivedFunctorPlus.map
            ((native_bounded_sh_comp B T.cf.i T.q T.cfg.i T.i_q).app K)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar B T.p)
          (lowerStar B T.cg.g)
          (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
            ((openImmersionLowerShriek B T.cfg.i).mapDerivedCategoryPlus.obj K) := by
  let := CompactSupportFormalism.HasBaseChange.isIso_baseChange
    (F := derivedPlusFormalism B) T.isPullback
  unfold native_bounded_triangle_iso
  rw [CompactSupportFormalism.compIso_hom_app (derivedPlusFormalism B) T K,
    derivedPlusFormalism_pfComp'_inv]
  rfl

private lemma generic_triangle_plus
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (μ : (openImmersionLowerShriek B T.cf.i).mapDerivedCategory ⋙
      (openImmersionLowerShriek B T.q).mapDerivedCategory ⟶
        (openImmersionLowerShriek B T.cfg.i).mapDerivedCategory)
    (ex : (lowerStar B T.cf.g).rightDerivedFunctor ⋙
      (openImmersionLowerShriek B T.cg.i).mapDerivedCategory ⟶
        (openImmersionLowerShriek B T.q).mapDerivedCategory ⋙
          (lowerStar B T.p).rightDerivedFunctor)
    (τ : rightDerivedLowerShriekOfCompactification B T.cf ⋙
      rightDerivedLowerShriekOfCompactification B T.cg ⟶
        rightDerivedLowerShriekOfCompactification B T.cfg)
    (μp : (openImmersionLowerShriek B T.cf.i).mapDerivedCategoryPlus ⋙
      (openImmersionLowerShriek B T.q).mapDerivedCategoryPlus ⟶
        (openImmersionLowerShriek B T.cfg.i).mapDerivedCategoryPlus)
    (exp : (lowerStar B T.cf.g).rightDerivedFunctorPlus ⋙
      (openImmersionLowerShriek B T.cg.i).mapDerivedCategoryPlus ⟶
        (openImmersionLowerShriek B T.q).mapDerivedCategoryPlus ⋙
          (lowerStar B T.p).rightDerivedFunctorPlus)
    (τp : rightDerivedLowerShriekOfCompactificationPlus B T.cf ⋙
      rightDerivedLowerShriekOfCompactificationPlus B T.cg ⟶
        rightDerivedLowerShriekOfCompactificationPlus B T.cfg)
    (hex₀ : ∀ M, DerivedCategory.Plus.ι.map
      (exp.app M) ≫
      (lowerStar B T.p).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek B T.q).mapDerivedCategoryPlus.obj M) =
    (openImmersionLowerShriek B T.cg.i).mapDerivedCategory.map
        ((lowerStar B T.cf.g).rightDerivedFunctorPlusCompatibility.hom.app M) ≫
      ex.app
        (DerivedCategory.Plus.ι.obj M))
    (hμ₀ : ∀ M, DerivedCategory.Plus.ι.map
      (μp.app M) =
    μ.app
      (DerivedCategory.Plus.ι.obj M))
    (hτ : ∀ M, τ.app M =
      (lowerStar B T.cg.g).rightDerivedFunctor.map
        (ex.app
            ((openImmersionLowerShriek B T.cf.i).mapDerivedCategory.obj M) ≫
          (lowerStar B T.p).rightDerivedFunctor.map
            (μ.app M)) ≫
        (Functor.rightDerivedFunctorCompIso' (lowerStar B T.p)
          (lowerStar B T.cg.g)
          (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
            ((openImmersionLowerShriek B T.cfg.i).mapDerivedCategory.obj M))
    (hτp : ∀ M, τp.app M =
      (lowerStar B T.cg.g).rightDerivedFunctorPlus.map
        (exp.app ((openImmersionLowerShriek B T.cf.i).mapDerivedCategoryPlus.obj M) ≫
          (lowerStar B T.p).rightDerivedFunctorPlus.map (μp.app M)) ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar B T.p)
          (lowerStar B T.cg.g)
          (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom.app
            ((openImmersionLowerShriek B T.cfg.i).mapDerivedCategoryPlus.obj M))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
    DerivedCategory.Plus.ι.map
        (τp.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        B T.cfg).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      B T.cg).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus
          B T.cf).obj K) ≫
      (rightDerivedLowerShriekOfCompactification B T.cg).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          B T.cf).hom.app K) ≫
      τ.app (DerivedCategory.Plus.ι.obj K) := by
  have hex := full_exact_exchange (lowerStar B T.cf.g)
    (openImmersionLowerShriek B T.cg.i) (openImmersionLowerShriek B T.q)
    (lowerStar B T.p) ex
    exp hex₀
  have hμ := full_exact_composition (openImmersionLowerShriek B T.cf.i)
    (openImmersionLowerShriek B T.q) (openImmersionLowerShriek B T.cfg.i)
    μ
    μp hμ₀
  have hν := full_proper_composition (lowerStar B T.p) (lowerStar B T.cg.g)
    (lowerStar B T.cfg.g)
    (Functor.rightDerivedFunctorCompIso' (lowerStar B T.p) (lowerStar B T.cg.g)
      (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom
    (Functor.rightDerivedFunctorPlusCompIso' (lowerStar B T.p) (lowerStar B T.cg.g)
      (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom
    (right_derived_comp_prime_plus (lowerStar B T.p) (lowerStar B T.cg.g)
      (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm))
  have h := restriction_triangle_transport
    (O := (openImmersionLowerShriek B T.cf.i).mapDerivedCategory)
    (R := (lowerStar B T.cf.g).rightDerivedFunctor)
    (J := (openImmersionLowerShriek B T.cg.i).mapDerivedCategory)
    (S := (lowerStar B T.cg.g).rightDerivedFunctor)
    (Q := (openImmersionLowerShriek B T.q).mapDerivedCategory)
    (P := (lowerStar B T.p).rightDerivedFunctor)
    (L := (openImmersionLowerShriek B T.cfg.i).mapDerivedCategory)
    (T := (lowerStar B T.cfg.g).rightDerivedFunctor)
    (Op := (openImmersionLowerShriek B T.cf.i).mapDerivedCategoryPlus)
    (Rp := (lowerStar B T.cf.g).rightDerivedFunctorPlus)
    (Jp := (openImmersionLowerShriek B T.cg.i).mapDerivedCategoryPlus)
    (Sp := (lowerStar B T.cg.g).rightDerivedFunctorPlus)
    (Qp := (openImmersionLowerShriek B T.q).mapDerivedCategoryPlus)
    (Pp := (lowerStar B T.p).rightDerivedFunctorPlus)
    (Lp := (openImmersionLowerShriek B T.cfg.i).mapDerivedCategoryPlus)
    (Tp := (lowerStar B T.cfg.g).rightDerivedFunctorPlus)
    (iC := DerivedCategory.Plus.ι) (iD := DerivedCategory.Plus.ι)
    (iY := DerivedCategory.Plus.ι) (iE := DerivedCategory.Plus.ι)
    (iZ := DerivedCategory.Plus.ι) (iW := DerivedCategory.Plus.ι)
    (openImmersionLowerShriek B T.cf.i).mapDerivedCategoryPlusCompatibility.hom
    (lowerStar B T.cf.g).rightDerivedFunctorPlusCompatibility.hom
    (openImmersionLowerShriek B T.cg.i).mapDerivedCategoryPlusCompatibility.hom
    (lowerStar B T.cg.g).rightDerivedFunctorPlusCompatibility.hom
    (openImmersionLowerShriek B T.q).mapDerivedCategoryPlusCompatibility.hom
    (lowerStar B T.p).rightDerivedFunctorPlusCompatibility.hom
    (openImmersionLowerShriek B T.cfg.i).mapDerivedCategoryPlusCompatibility.hom
    (lowerStar B T.cfg.g).rightDerivedFunctorPlusCompatibility.hom
    ex
    μ
    (Functor.rightDerivedFunctorCompIso' (lowerStar B T.p) (lowerStar B T.cg.g)
      (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm)).hom
    exp
    μp
    (Functor.rightDerivedFunctorPlusCompIso' (lowerStar B T.p) (lowerStar B T.cg.g)
      (lowerStarComp B T.p T.cg.g T.cfg.g T.p_g.symm )).hom hex hμ hν
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B T.cf).hom
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B T.cg).hom
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B T.cfg).hom
    (candidate_compat_nt B T.cf)
    (candidate_compat_nt B T.cg)
    (candidate_compat_nt B T.cfg)
    τ
    τp
    hτ hτp K
  exact h

private lemma triangle_comp_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((native_bounded_triangle_iso (ModuleCat.{u + 1} A) T).hom.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) T.cfg).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) T.cg).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) T.cf).obj K) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) T.cf).hom.app K) ≫
      (native_unbounded_triangle_iso A T).hom.app (DerivedCategory.Plus.ι.obj K) := by
  let := bounded_open_isIso A T.isPullback
  exact generic_triangle_plus (ModuleCat.{u + 1} A) T
    (unbounded_sh_comp_map A T.cf.i T.q T.cfg.i T.i_q)
    (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) T.isPullback)
    (native_unbounded_triangle_iso A T).hom
    (native_bounded_sh_comp (ModuleCat.{u + 1} A) T.cf.i T.q T.cfg.i T.i_q)
    (native_bounded_exchange (ModuleCat.{u + 1} A) T.isPullback)
    (native_bounded_triangle_iso (ModuleCat.{u + 1} A) T).hom
    (proper_open_exchange_plus A T.isPullback)
    (bounded_sh_comp_plus A T.cf.i T.q T.cfg.i T.i_q)
    (unbounded_tower_app A T)
    (bounded_tower_app_generic (ModuleCat.{u + 1} A) T) K

private lemma compositor_iso_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {H₀ H₁ : C ⥤ E}
    {ε ε' : F₀ ⋙ G₀ ≅ H₀} {α α' : F₀ ≅ F₁} {β β' : G₀ ≅ G₁}
    {δ δ' : F₁ ⋙ G₁ ≅ H₁} {γ γ' : H₁ ≅ H₀}
    (hε : ε = ε') (hα : α = α') (hβ : β = β') (hδ : δ = δ') (hγ : γ = γ')
    (h : ε.hom = NatTrans.hcomp α.hom β.hom ≫ δ.hom ≫ γ.hom) :
    ε'.hom = NatTrans.hcomp α'.hom β'.hom ≫ δ'.hom ≫ γ'.hom := by
  subst ε' α' β' δ' γ'
  exact h

private lemma restriction_compositor_paste
    {C D E Cp Dp Ep : Type*}
    [Category C] [Category D] [Category E] [Category Cp] [Category Dp] [Category Ep]
    {iC : Cp ⥤ C} {iD : Dp ⥤ D} {iE : Ep ⥤ E}
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {H₀ H₁ : C ⥤ E}
    {Fp₀ Fp₁ : Cp ⥤ Dp} {Gp₀ Gp₁ : Dp ⥤ Ep} {Hp₀ Hp₁ : Cp ⥤ Ep}
    (κF₀ : Fp₀ ⋙ iD ⟶ iC ⋙ F₀) (κF₁ : Fp₁ ⋙ iD ⟶ iC ⋙ F₁)
    (κG₀ : Gp₀ ⋙ iE ⟶ iD ⋙ G₀) (κG₁ : Gp₁ ⋙ iE ⟶ iD ⋙ G₁)
    (κH₀ : Hp₀ ⋙ iE ⟶ iC ⋙ H₀) (κH₁ : Hp₁ ⋙ iE ⟶ iC ⋙ H₁)
    (α : F₀ ⟶ F₁) (β : G₀ ⟶ G₁) (δ : F₁ ⋙ G₁ ⟶ H₁) (γ : H₁ ⟶ H₀)
    (αp : Fp₀ ⟶ Fp₁) (βp : Gp₀ ⟶ Gp₁) (δp : Fp₁ ⋙ Gp₁ ⟶ Hp₁) (γp : Hp₁ ⟶ Hp₀)
    (hα : ∀ K, iD.map (αp.app K) ≫ κF₁.app K = κF₀.app K ≫ α.app (iC.obj K))
    (hβ : ∀ K, iE.map (βp.app K) ≫ κG₁.app K = κG₀.app K ≫ β.app (iD.obj K))
    (hδ : ∀ K, iE.map (δp.app K) ≫ κH₁.app K =
      κG₁.app (Fp₁.obj K) ≫ G₁.map (κF₁.app K) ≫ δ.app (iC.obj K))
    (hγ : ∀ K, iE.map (γp.app K) ≫ κH₀.app K = κH₁.app K ≫ γ.app (iC.obj K))
    (ε : F₀ ⋙ G₀ ⟶ H₀) (εp : Fp₀ ⋙ Gp₀ ⟶ Hp₀)
    (hε : ε = NatTrans.hcomp α β ≫ δ ≫ γ)
    (hεp : εp = NatTrans.hcomp αp βp ≫ δp ≫ γp)
    (K : Cp) :
    iE.map (εp.app K) ≫ κH₀.app K =
      κG₀.app (Fp₀.obj K) ≫ G₀.map (κF₀.app K) ≫ ε.app (iC.obj K) := by
  rw [hε, hεp]
  have hαβ := restriction_hcomp_comp κF₀ κF₁ κG₀ κG₁ α β αp βp hα hβ
  have hδ' : ∀ K, iE.map (δp.app K) ≫ κH₁.app K =
      (restriction_comp κF₁ κG₁).app K ≫ δ.app (iC.obj K) := by
    intro M
    simpa only [restriction_comp_app, Category.assoc] using hδ M
  have h₁ := restriction_trans iC iE (F₀ ⋙ G₀) (F₁ ⋙ G₁) H₁
    (Fp₀ ⋙ Gp₀) (Fp₁ ⋙ Gp₁) Hp₁ (restriction_comp κF₀ κG₀)
    (restriction_comp κF₁ κG₁) κH₁ (NatTrans.hcomp α β) δ
    (NatTrans.hcomp αp βp) δp hαβ hδ'
  have h₂ := restriction_trans iC iE (F₀ ⋙ G₀) H₁ H₀
    (Fp₀ ⋙ Gp₀) Hp₁ Hp₀ (restriction_comp κF₀ κG₀) κH₁ κH₀
    (NatTrans.hcomp α β ≫ δ) γ (NatTrans.hcomp αp βp ≫ δp) γp h₁ hγ K
  simpa only [Category.assoc, restriction_comp_app] using h₂

private lemma compositor_middle_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E} {H₀ H₁ : C ⥤ E}
    (ε : F₀ ⋙ G₀ ⟶ H₀) (α : F₀ ⟶ F₁) (β : G₀ ⟶ G₁) (γ : H₁ ⟶ H₀)
    {δ δ' : F₁ ⋙ G₁ ⟶ H₁} (hδ : δ = δ')
    (h : ε = NatTrans.hcomp α β ≫ δ ≫ γ) :
    ε = NatTrans.hcomp α β ≫ δ' ≫ γ := by
  subst δ'
  exact h

private lemma native_bounded_triangle_iso_eq
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [(derivedPlusFormalism B).HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    native_bounded_triangle_iso B T = (derivedPlusFormalism B).compIso T := rfl

private lemma native_unbounded_triangle_ofRestrict
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    native_unbounded_triangle_iso A (Compactification.Triangle.ofRestrict d e) =
      rightDerivedLowerShriekOfCompactificationCompIso A d e :=
  unbounded_comp_iso A d e

end CompositionRestriction

section CompositionPlus

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] AlgebraicGeometry.Etale.DerivedCategoryModule._proof_1
  AlgebraicGeometry.Etale.DerivedCategoryModule._proof_2
attribute [local irreducible] Compactification.ofComp Compactification.restrict
  Compactification.comp
attribute [local irreducible] native_unbounded_triangle_iso native_bounded_triangle_iso
  rightDerivedLowerShriekOfCompactificationPlusCompatibility

private theorem inverse_iso_paste
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F F' : C ⥤ D} (G : D ⥤ E) {H J : C ⥤ E}
    (a : H ≅ J) (b : J ≅ F ⋙ G) (c : F ≅ F') :
    (a ≪≫ b ≪≫ Functor.isoWhiskerRight c G).inv =
      NatTrans.hcomp c.inv (𝟙 G) ≫ b.inv ≫ a.inv := by
  ext K
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, NatTrans.hcomp_app, NatTrans.id_app,
    Category.assoc]
  erw [Category.id_comp]

private theorem comparison_inverse_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (cf cd : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A cf cd).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) cd).hom.app L =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cf).hom.app L ≫
      (rightDerivedLowerShriekOfCompactificationIso A cd cf).inv.app
        (DerivedCategory.Plus.ι.obj L) := by
  have hi := square_inverse
    (DerivedCategory.Plus.ι.mapIso
      ((rightDerivedLowerShriekOfCompactificationPlusIso A cd cf).app L))
    ((rightDerivedLowerShriekOfCompactificationIso A cd cf).app (DerivedCategory.Plus.ι.obj L))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cd).hom.app L)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) cf).hom.app L)
    (unboundedEtaleCompactSupport_comparison_plus A f cd cf L)
  simpa only [Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
    ← rightDerivedLowerShriekOfCompactificationPlusIso_symm A cd cf,
    Iso.symm_hom] using hi

private theorem comparison_self_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map
        ((rightDerivedLowerShriekOfCompactificationPlusIso A c c).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app L =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app L ≫
      (𝟙 _ : rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c ⟶ _).app (DerivedCategory.Plus.ι.obj L) := by
  simp only [rightDerivedLowerShriekOfCompactificationPlusIso_refl,
    Iso.refl_hom, NatTrans.id_app]
  erw [DerivedCategory.Plus.ι.map_id, Category.id_comp, Category.comp_id]

private theorem triangle_restriction_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cfg : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (ε : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf ⋙
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg ⟶
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg)
    (εp : rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf ⋙
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) T.cg ⟶
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cfg)
    (hu : ε = NatTrans.hcomp
          (rightDerivedLowerShriekOfCompactificationIso A T.cf cf).inv
          (𝟙 (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) T.cg)) ≫
        (native_unbounded_triangle_iso A T).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A T.cfg cfg).hom)
    (hb : εp = NatTrans.hcomp
          (rightDerivedLowerShriekOfCompactificationPlusIso A cf T.cf).hom
          (rightDerivedLowerShriekOfCompactificationPlusIso A T.cg T.cg).hom ≫
        (native_bounded_triangle_iso (ModuleCat.{u + 1} A) T).hom ≫
        (rightDerivedLowerShriekOfCompactificationPlusIso A T.cfg cfg).hom)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    DerivedCategory.Plus.ι.map (εp.app K) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility B cfg).hom.app K =
    (rightDerivedLowerShriekOfCompactificationPlusCompatibility B T.cg).hom.app
        ((rightDerivedLowerShriekOfCompactificationPlus B cf).obj K) ≫
      (rightDerivedLowerShriekOfCompactification B T.cg).map
        ((rightDerivedLowerShriekOfCompactificationPlusCompatibility B cf).hom.app K) ≫
      ε.app (DerivedCategory.Plus.ι.obj K) := by
  dsimp only
  rw [hu, hb]
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [unboundedEtaleCompactSupport_comparison_plus A (f ≫ g) T.cfg cfg K]
  rw [reassoc_of% (triangle_comp_plus A T K)]
  simp only [NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  have hn := (rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) T.cg).hom.naturality
    ((rightDerivedLowerShriekOfCompactificationPlusIso A cf T.cf).hom.app K)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [reassoc_of% (comparison_self_plus A g T.cg
    ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) cf).obj K))]
  simp only [NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [comparison_inverse_plus A f cf T.cf K]
  simp only [Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc]

/-- The normalized composition comparison restricts to the existing bounded-below one.
Source: Stacks Project, Tags 0F7H--0F7K
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: compare two compactifications through their common infimum, using the
bounded/unbounded refinement squares; invert the second square and paste it with the first.
For the chosen `ofRestrict` triangle, use this comparison on its first and composite faces,
and the identity on its second face. The bounded and native compositor definitions give the
same triangle word, and naturality pastes the four faces. No Noetherian, separatedness or
finite-type hypothesis is used. -/
theorem unboundedEtaleCompactSupport_composition_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    DerivedCategory.Plus.ι.map ((rightDerivedLowerShriekPlusCompIso A f g).hom.app K) ≫
      (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K =
    (rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) g).hom.app
        ((rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj K) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        ((rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A) f).hom.app K) ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom.app (DerivedCategory.Plus.ι.obj K) := by
  let B := ModuleCat.{u + 1} A
  let d := HasCompactification.compactification g
  let e := (HasCompactification.compactification (f ≫ g)).ofComp d
  let T := Compactification.Triangle.ofRestrict d e
  let cf := HasCompactification.compactification f
  let cfg := HasCompactification.compactification (f ≫ g)
  have hb := compositor_middle_transport _ _ _ _
    (congrArg Iso.hom (native_bounded_triangle_iso_eq B T).symm)
    (rightDerivedLowerShriekPlusCompIso_hom_eq A T)
  have hu : (unboundedEtaleLowerShriekCompIso A f g).hom =
      NatTrans.hcomp (rightDerivedLowerShriekIso A e.restrict).inv
          (𝟙 (rightDerivedLowerShriek B g)) ≫
        (native_unbounded_triangle_iso A T).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A T.cfg cfg).hom := by
    rw [native_unbounded_triangle_ofRestrict]
    have h := inverse_iso_paste (rightDerivedLowerShriek B g)
      (rightDerivedLowerShriekIso A (d.comp e)).symm
      (rightDerivedLowerShriekOfCompactificationCompIso A d e).symm
      (rightDerivedLowerShriekIso A e.restrict)
    simp only [Iso.symm_inv] at h
    refine Eq.trans ?_ h
    simp only [unboundedEtaleLowerShriekCompIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, d, e]
    exact (Category.assoc _ _ _).symm
  exact triangle_restriction_plus A f g cf cfg T
    (unboundedEtaleLowerShriekCompIso A f g).hom
    (rightDerivedLowerShriekPlusCompIso A f g).hom hu hb K

end CompositionPlus

end BoundedBelowRestriction

open CategoryTheory.Abelian
@[irreducible]
private noncomputable def right_derived_identity_iso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C]
    (T : C ⥤ C) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (e : T ≅ 𝟭 C) :
    T.rightDerivedFunctor ≅ 𝟭 (DerivedCategory C) :=
  T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C

private lemma right_derived_identity_iso_eq
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasKInjectiveResolutions C]
    (T : C ⥤ C) [T.Additive]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T] (e : T ≅ 𝟭 C) :
    right_derived_identity_iso T e =
      T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C := by
  unfold right_derived_identity_iso
  rfl

section NormalizationModels
universe w₁ w₂ v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  [HasKInjectiveResolutions C]
private noncomputable def right_unit_Q (F : C ⥤ D) [F.Additive]
    (J : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj J) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj J) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app J)
private lemma right_unit_Q_obj_iso (F : C ⥤ D) [F.Additive]
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    right_unit_Q F J ≫ (F.rightDerivedFunctorObjQIso J).hom = 𝟙 _ := by
  simp [right_unit_Q, Functor.rightDerivedFunctorObjQIso,
    Category.assoc]
private lemma right_unit_Q_naturality (F : C ⥤ D) [F.Additive]
    {J I : CochainComplex C ℤ} (ρ : J ⟶ I) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ρ) ≫ right_unit_Q F I =
      right_unit_Q F J ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map ρ) := by
  have h := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient C (.up ℤ)).map ρ)
  simp only [Functor.comp_map] at h
  simp only [right_unit_Q, Category.assoc]
  rw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hf : ((F.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient C (.up ℤ)).map ρ)) =
    (HomotopyCategory.quotient D (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map ρ) := rfl
  rw [← hf, reassoc_of% h, ← Functor.map_comp]
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  rw [Functor.map_comp]
omit [HasKInjectiveResolutions C] in
private lemma exact_factor_Q (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj J) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app J) ≫
      F.mapDerivedCategoryFactors.hom.app J =
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj J) := by
  have he : F.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj J) =
    F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app J) ≪≫
      F.mapDerivedCategoryFactors.app J ≪≫
        ((DerivedCategory.quotientCompQhIso D).app
          ((F.mapHomologicalComplex (.up ℤ)).obj J)).symm := by
    apply Iso.ext
    simp only [Iso.app_hom, Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom,
      Functor.mapDerivedCategoryFactorsh_hom_app, Functor.mapHomotopyCategoryFactors,
      Quotient.lift.isLift_inv]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
    rfl
  have hi := congrArg Iso.inv he
  change F.mapDerivedCategoryFactorsh.inv.app _ = _ at hi
  rw [hi]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv,
    Iso.app_hom, Category.assoc, ]
  rw [← F.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, F.mapDerivedCategory.map_id,
    Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
private lemma right_unit_Q_exact_fac (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex C ℤ) :
    right_unit_Q F J ≫ F.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj J) ≫ F.mapDerivedCategoryFactors.hom.app J = 𝟙 _ := by
  have hn := F.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app J)
  simp only [right_unit_Q, Category.assoc]
  rw [reassoc_of% hn]
  have hF := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.quotient C (.up ℤ)).obj J)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hF
  rw [← Category.assoc _ _ (F.mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso C).hom.app J) ≫
      F.mapDerivedCategoryFactors.hom.app J), hF]
  rw [exact_factor_Q F J, Iso.inv_hom_id_app]

private lemma exact_iso_obj_model (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    F.rightDerivedFunctorIsoMapDerivedCategory.inv.app (DerivedCategory.Q.obj J) ≫
      (F.rightDerivedFunctorObjQIso J).hom = F.mapDerivedCategoryFactors.hom.app J := by
  have : IsIso (right_unit_Q F J) := by
    dsimp only [right_unit_Q]
    infer_instance
  rw [← cancel_epi (right_unit_Q F J ≫
    F.rightDerivedFunctorIsoMapDerivedCategory.hom.app (DerivedCategory.Q.obj J))]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [right_unit_Q_obj_iso, right_unit_Q_exact_fac]
omit [HasKInjectiveResolutions C] in
private lemma derived_id_Q_fac (J : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj J) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app J := by
  let q := DerivedCategory.quotientCompQhIso C
  have hn := (Functor.mapDerivedCategoryIdIso C).hom.naturality (q.hom.app J)
  simp only [Functor.id_map] at hn
  rw [← cancel_epi ((𝟭 C).mapDerivedCategory.map (q.hom.app J))]
  erw [hn, Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Category.assoc]
  erw [DerivedCategory.Qh.map_id, Category.id_comp]
  change _ ≫ _ ≫ (q.inv.app J ≫ q.hom.app J) = _
  rw [Iso.inv_hom_id_app, Category.comp_id]

private lemma identity_derived_obj_model (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (e : F ≅ 𝟭 C)
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    (F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C
      ).inv.app (DerivedCategory.Q.obj J) ≫ (F.rightDerivedFunctorObjQIso J).hom =
      DerivedCategory.Q.map ((e.inv.mapHomologicalComplex (.up ℤ)).app J) := by
  simp only [Iso.trans_inv, NatTrans.comp_app, Category.assoc]
  rw [exact_iso_obj_model F J]
  have he := Functor.mapDerivedCategoryNatIso_fac e.symm J
  simp only [Functor.mapDerivedCategoryNatIso_symm, Iso.symm_hom] at he
  rw [he, ← derived_id_Q_fac J]
  simp only [Iso.inv_hom_id_app_assoc]
universe w₃ v₃ u₃
variable {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]

private lemma natTrans_ext_kInjective
    {F G : DerivedCategory C ⥤ DerivedCategory E} (α β : F ⟶ G)
    (h : ∀ (M : CochainComplex C ℤ) [M.IsKInjective],
      α.app (DerivedCategory.Q.obj M) = β.app (DerivedCategory.Q.obj M)) : α = β := by
  apply NatTrans.ext
  funext K
  obtain ⟨M, hM, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  let := hM
  apply (cancel_mono (G.map e.hom)).1
  rw [← α.naturality, ← β.naturality, h M]

private lemma comparison_model_on_injective
    [HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E) (T : C ⥤ C)
    [S.Additive] [O.Additive] [R.Additive] [T.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (e : T ≅ 𝟭 C) (θ : T ⋙ S ⟶ O ⋙ R) (a : S ⟶ O ⋙ R)
    (σ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (Γ : T.rightDerivedFunctor ⋙ S.mapDerivedCategory ⟶
      O.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (hσ : ∀ M : CochainComplex C ℤ,
      σ.app (DerivedCategory.Q.obj M) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.hom.app M) =
      S.mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app M) ≫
        right_unit_Q R ((O.mapHomologicalComplex (.up ℤ)).obj M))
    (ha : ∀ M : CochainComplex C ℤ,
      (a.mapHomologicalComplex (.up ℤ)).app M =
        (S.mapHomologicalComplex (.up ℤ)).map
          ((e.inv.mapHomologicalComplex (.up ℤ)).app M) ≫
        (θ.mapHomologicalComplex (.up ℤ)).app M)
    (hΓ : ∀ (M : CochainComplex C ℤ) [M.IsKInjective]
      (N : CochainComplex D ℤ) [N.IsKInjective]
      (ρ : (O.mapHomologicalComplex (.up ℤ)).obj M ⟶ N) [QuasiIso ρ],
      S.mapDerivedCategory.map ((T.rightDerivedFunctorObjQIso M).hom) ≫
        S.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((θ.mapHomologicalComplex (.up ℤ)).app M) ≫
        DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map ρ) =
      Γ.app (DerivedCategory.Q.obj M) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.hom.app M ≫
          DerivedCategory.Q.map ρ) ≫ (R.rightDerivedFunctorObjQIso N).hom)
    (M : CochainComplex C ℤ) [M.IsKInjective] :
    σ.app (DerivedCategory.Q.obj M) =
      S.mapDerivedCategory.map
        ((right_derived_identity_iso T e).inv.app (DerivedCategory.Q.obj M)) ≫
        Γ.app (DerivedCategory.Q.obj M) := by
  unfold right_derived_identity_iso
  obtain ⟨N, hN, ρ, hρ, _⟩ := HasKInjectiveResolutions.exists_isKInjective
    ((O.mapHomologicalComplex (.up ℤ)).obj M)
  let := hN
  let := hρ
  let t := R.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.hom.app M ≫
    DerivedCategory.Q.map ρ) ≫ (R.rightDerivedFunctorObjQIso N).hom
  have : IsIso t := by dsimp only [t]; infer_instance
  apply (cancel_mono t).1
  let z := S.mapDerivedCategoryFactors.hom.app M ≫
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app M) ≫
    DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map ρ)
  have hleft : σ.app (DerivedCategory.Q.obj M) ≫ t = z := by
    dsimp only [t, z]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hσ M)]
    rw [← reassoc_of% (right_unit_Q_naturality R ρ)]
    rw [right_unit_Q_obj_iso, Category.comp_id]
  have hright : S.mapDerivedCategory.map
      ((T.rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C
        ).inv.app (DerivedCategory.Q.obj M)) ≫
      Γ.app (DerivedCategory.Q.obj M) ≫ t = z := by
    dsimp only [t, z]
    rw [← hΓ M N ρ]
    rw [← S.mapDerivedCategory.map_comp_assoc, identity_derived_obj_model T e M]
    have hn := S.mapDerivedCategoryFactors.hom.naturality
      ((e.inv.mapHomologicalComplex (.up ℤ)).app M)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← DerivedCategory.Q.map_comp_assoc, ← ha M]
    rfl
  simpa only [Category.assoc] using hleft.trans hright.symm
omit [HasKInjectiveResolutions C] in
private lemma comparison_complex_fac
    [HasKInjectiveResolutions D]
    (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [S.Additive] [O.Additive] [R.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits O] [PreservesFiniteColimits O]
    (a : S ⟶ O ⋙ R)
    (σ : S.mapDerivedCategory ⟶ O.mapDerivedCategory ⋙ R.rightDerivedFunctor)
    (hσ : ∀ K : HomotopyCategory C (.up ℤ),
      σ.app (DerivedCategory.Qh.obj K) =
        S.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).app K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)).inv.app K) ≫
        R.rightDerivedFunctorUnit.app ((O.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactorsh.inv.app K))
    (J : CochainComplex C ℤ) :
    σ.app (DerivedCategory.Q.obj J) ≫
        R.rightDerivedFunctor.map (O.mapDerivedCategoryFactors.hom.app J) =
      S.mapDerivedCategoryFactors.hom.app J ≫
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app J) ≫
        right_unit_Q R ((O.mapHomologicalComplex (.up ℤ)).obj J) := by
  let q := DerivedCategory.quotientCompQhIso C
  have hn := σ.naturality (q.hom.app J)
  simp only [Functor.comp_map] at hn
  rw [← cancel_epi (S.mapDerivedCategory.map (q.hom.app J))]
  rw [reassoc_of% hn, hσ]
  simp only [Category.assoc]
  slice_lhs 5 7 =>
    rw [← R.rightDerivedFunctor.map_comp_assoc, ← R.rightDerivedFunctor.map_comp,
      Category.assoc, exact_factor_Q O J]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have hc : (Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)
      ).inv.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J) = 𝟙 _ := by
    rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (O ⋙ R)) (.up ℤ)
      ).hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj J))]
    rw [Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
    exact (Category.comp_id _).symm
  rw [hc]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv, Category.assoc]
  erw [DerivedCategory.Qh.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.id_comp]
  have ha : (a.mapHomotopyCategory (.up ℤ)).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj J) =
    (HomotopyCategory.quotient _ (.up ℤ)).map
      ((a.mapHomologicalComplex (.up ℤ)).app J) := rfl
  erw [ha, DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  rfl

private lemma theta_normalization
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [HasSmallSiteSheafify B]
    {X C D : Scheme.{u}} (j : X ⟶ C) (q : C ⟶ D) (k : X ⟶ D)
    [IsOpenImmersion j] [IsOpenImmersion k] (hk : j ≫ q = k)
    (θ : lowerStar B (𝟙 X) ⋙ openImmersionLowerShriek B k ≅
      openImmersionLowerShriek B j ⋙ lowerStar B q)
    (hθ : ∀ M, θ.hom.app M ≫
      (lowerStar B q).map ((openImmersionLowerShriekToLowerStar B j).app M) ≫
      (lowerStarComp B j q).hom.app M =
        (openImmersionLowerShriekToLowerStar B k).app ((lowerStar B (𝟙 X)).obj M) ≫
        (lowerStarComp B (𝟙 X) k (j ≫ q) (by simp [hk])).hom.app M)
    (M : Sheaf X.smallEtaleTopology B) :
    (openImmersionLowerShriek B k).map ((lowerStarId B X).inv.app M) ≫
      θ.hom.app M ≫
      (lowerStar B q).map ((openImmersionLowerShriekToLowerStar B j).app M) ≫
      (lowerStarComp B j q k hk.symm).hom.app M =
        (openImmersionLowerShriekToLowerStar B k).app M := by
  subst k
  rw [hθ, lowerStarComp_id_left]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  rw [← (openImmersionLowerShriekToLowerStar B (j ≫ q)).naturality_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  dsimp only [Functor.id_obj]
  erw [Category.comp_id]

private lemma open_sheaf_comparison
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U Z : Scheme.{u}} (k : U ⟶ Z) [IsOpenImmersion k]
    (M : Sheaf U.smallEtaleTopology B) :
    etaleLowerShriekToLowerStar B k M =
      (openImmersionLowerShriekToLowerStar B k).app M := by
  have he : (lowerStarUnit B k).app M =
      inv ((openImmersionRestrictionLowerStarAdjunction B k).counit.app M) := by
    apply (cancel_mono ((openImmersionRestrictionLowerStarAdjunction B k).counit.app M)).1
    rw [IsIso.inv_hom_id]
    exact congr_app (lowerStarUnit_comp_counit B k) M
  rw [etaleLowerShriekToLowerStar, etaleLowerShriekRestrictionAdjunction,
    etaleLowerShriekUpperStarAdjunction]
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  simp only [Iso.symm_inv, Category.assoc, ]
  rw [he, Adjunction.homEquiv_counit]
  rw [openImmersionLowerShriekToLowerStar_app]
  simp only [ Iso.inv_hom_id_app, Category.comp_id,
    NatIso.isIso_inv_app]
  rfl

private lemma identity_prepend_app
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {R : C ⥤ C} {G : C ⥤ D}
    (e : R ≅ 𝟭 C) (γ : R ⋙ F ≅ G) (M : C) :
    ((Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.symm F ≪≫ γ).hom.app M =
      F.map (e.inv.app M) ≫ γ.hom.app M := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    Category.id_comp]

private lemma prepend_complex_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (T : C ⥤ C) (S : C ⥤ E) (O : C ⥤ D) (R : D ⥤ E)
    [T.Additive] [S.Additive] [O.Additive] [R.Additive]
    (e : T ≅ 𝟭 C) (θ : T ⋙ S ⟶ O ⋙ R) (J : CochainComplex C ℤ) :
    (((Functor.leftUnitor S).inv ≫ Functor.whiskerRight e.inv S ≫ θ
      ).mapHomologicalComplex (.up ℤ)).app J =
      (S.mapHomologicalComplex (.up ℤ)).map
          ((e.inv.mapHomologicalComplex (.up ℤ)).app J) ≫
        (θ.mapHomologicalComplex (.up ℤ)).app J := by
  ext n : 1
  simp only [NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.leftUnitor_inv_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
set_option maxRecDepth 2048 in
private lemma normalization_open_interchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian Z]
    (k : U ⟶ Z) [IsOpenImmersion k] (c : Compactification k) [IsNoetherian c.Z]
    (N : EtaleCompactSupportNormalization A)
    (θ : lowerStar (ModuleCat.{u + 1} A) (𝟙 U) ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) k ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (Γ : (lowerStar (ModuleCat.{u + 1} A) (𝟙 U)).rightDerivedFunctor ⋙
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor)
    (hθ : ∀ M, θ.hom.app M ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g).hom.app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app
        ((lowerStar (ModuleCat.{u + 1} A) (𝟙 U)).obj M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (𝟙 U) k (c.i ≫ c.g)
        (by simpa using c.comm.symm)).hom.app M)
    (hΓ : ∀ (M : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      [M.IsKInjective]
      (I : CochainComplex (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      [I.IsKInjective]
      (ρ : ((openImmersionLowerShriek
        (ModuleCat.{u + 1} A) c.i).mapHomologicalComplex (.up ℤ)).obj M ⟶ I) [QuasiIso ρ],
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          (((lowerStar (ModuleCat.{u + 1} A) (𝟙 U)).rightDerivedFunctorObjQIso M).hom) ≫
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k).mapDerivedCategoryFactors.hom.app
          (((lowerStar (ModuleCat.{u + 1} A) (𝟙 U)).mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((θ.hom.mapHomologicalComplex (.up ℤ)).app M) ≫
        DerivedCategory.Q.map
          (((lowerStar (ModuleCat.{u + 1} A) c.g).mapHomologicalComplex (.up ℤ)).map ρ) =
      Γ.hom.app (DerivedCategory.Q.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          ((openImmersionLowerShriek
            (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.hom.app M ≫
            DerivedCategory.Q.map ρ) ≫
        ((lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorObjQIso I).hom) :
    (N.comparison k c).inv =
      ((Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
        ((right_derived_identity_iso
          (lowerStar (ModuleCat.{u + 1} A) (𝟙 U))
          (lowerStarId (ModuleCat.{u + 1} A) U)).symm) _ ≪≫ Γ).hom := by
  let : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  let : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  let : IsNoetherian c.Z := ⟨⟩
  let a : (openImmersionLowerShriek (ModuleCat.{u + 1} A) k) ⟶ (openImmersionLowerShriek
      (ModuleCat.{u + 1} A) c.i) ⋙ (lowerStar (ModuleCat.{u + 1} A) c.g) :=
    (Functor.leftUnitor (openImmersionLowerShriek (ModuleCat.{u + 1} A) k)).inv ≫
        Functor.whiskerRight (lowerStarId (ModuleCat.{u + 1} A) U).inv (openImmersionLowerShriek
        (ModuleCat.{u + 1} A) k) ≫ θ.hom
  have hs : N.sheafComparison k c = a := by
    apply NatTrans.ext
    funext M
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app M) := open_compare_mono A c.i M
    have : Mono ((compactificationSheafToDirectImage A c).app M) := by
      dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
        Functor.whiskerRight_app]
      infer_instance
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app M)).1
    rw [N.sheaf_normalization]
    have he := theta_normalization (ModuleCat.{u + 1} A) c.i c.g k c.comm.symm θ hθ M
    rw [open_sheaf_comparison]
    simp only [a, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_inv_app, compactificationSheafToDirectImage,
       Category.assoc]
    erw [Category.id_comp]
    convert! he.symm using 1
  let σ := compactSupportDerivedComparison A k c a
  have hσ : (N.comparison k c).inv = σ := by
    apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) _
      ).faithful.map_injective
    apply NatTrans.ext
    funext M
    change (N.comparison k c).inv.app (DerivedCategory.Qh.obj M) =
      σ.app (DerivedCategory.Qh.obj M)
    rw [N.derived_normalization, compactSupportDerivedComparison_app, hs]
  have hfac (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
      σ.app (DerivedCategory.Q.obj J) ≫
          (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map ((openImmersionLowerShriek
              (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.hom.app J) =
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategoryFactors.hom.app J ≫
          DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).app J) ≫
          right_unit_Q (lowerStar (ModuleCat.{u + 1} A) c.g) (((openImmersionLowerShriek
              (ModuleCat.{u + 1} A) c.i).mapHomologicalComplex (.up ℤ)).obj J) :=
    comparison_complex_fac
      (C := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (D := Sheaf c.Z.smallEtaleTopology
          (ModuleCat.{u + 1} A))
      (E := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (openImmersionLowerShriek
          (ModuleCat.{u + 1} A) k) (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i) (lowerStar
          (ModuleCat.{u + 1} A) c.g) a σ
      (compactSupportDerivedComparison_app A k c a) J
  have ha (J : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
      (a.mapHomologicalComplex (.up ℤ)).app J =
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapHomologicalComplex (.up ℤ)).map
            (((lowerStarId (ModuleCat.{u + 1} A) U).inv.mapHomologicalComplex (.up ℤ)).app J) ≫
          (θ.hom.mapHomologicalComplex (.up ℤ)).app J :=
    prepend_complex_fac (lowerStar (ModuleCat.{u + 1} A) (𝟙 U)) (openImmersionLowerShriek
        (ModuleCat.{u + 1} A) k) (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i) (lowerStar
        (ModuleCat.{u + 1} A) c.g) (lowerStarId (ModuleCat.{u + 1} A) U) θ.hom J
  clear_value σ a
  rw [hσ]
  apply natTrans_ext_kInjective
    (C := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (E := Sheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} A))
  intro M hM
  let := hM
  have hh := comparison_model_on_injective
    (C := Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (D := Sheaf c.Z.smallEtaleTopology
        (ModuleCat.{u + 1} A))
    (E := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (openImmersionLowerShriek
        (ModuleCat.{u + 1} A) k) (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i) (lowerStar
        (ModuleCat.{u + 1} A) c.g) (lowerStar (ModuleCat.{u + 1} A) (𝟙 U)) (lowerStarId
        (ModuleCat.{u + 1} A) U) θ.hom a σ Γ.hom
    hfac ha hΓ M
  have hc := identity_prepend_app (openImmersionLowerShriek (ModuleCat.{u + 1} A)
      k).mapDerivedCategory (right_derived_identity_iso (lowerStar (ModuleCat.{u + 1} A) (𝟙 U))
      (lowerStarId (ModuleCat.{u + 1} A) U)) Γ
    (DerivedCategory.Q.obj M)
  exact hh.trans hc.symm
end NormalizationModels
section NormalizationRefinements
attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

private lemma adjunct_eq_inverse
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {X : C} {Y : D} (φ : L.obj X ⟶ Y)
    (e : R.obj Y ≅ X) (hφ : adj.homEquiv _ _ φ ≫ e.hom = 𝟙 X) :
    φ = L.map e.inv ≫ adj.counit.app Y := by
  apply (adj.homEquiv _ _).injective
  have hs := adj.homEquiv_counit (g := e.inv)
  have hh : adj.homEquiv X Y (L.map e.inv ≫ adj.counit.app Y) = e.inv := by
    rw [← hs]
    exact Equiv.apply_symm_apply _ _
  rw [hh]
  apply (cancel_mono e.hom).1
  rw [hφ, e.inv_hom_id]

private noncomputable def refinement_transport
    (F : CompactSupportFormalism.{_, _, u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (β : F.sh d.i ⟶ F.sh c.i ⋙ F.pf r.hom) :
    F.shriek d ⟶ F.shriek c :=
  Functor.whiskerRight β (F.pf d.g) ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.sh c.i) (F.pfComp' r.hom d.g c.g r.hom_g).inv
private lemma refinement_transport_app
    (F : CompactSupportFormalism.{_, _, u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (β : F.sh d.i ⟶ F.sh c.i ⋙ F.pf r.hom) (K : F.obj X) :
    (refinement_transport F r β).app K =
      (F.pf d.g).map (β.app K) ≫
        (F.pfComp' r.hom d.g c.g r.hom_g).inv.app ((F.sh c.i).obj K) := by
  simp only [refinement_transport, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp]
private lemma refinement_transport_comp
    (F : CompactSupportFormalism.{_, _, u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e)
    (βr : F.sh d.i ⟶ F.sh c.i ⋙ F.pf r.hom)
    (βs : F.sh e.i ⟶ F.sh d.i ⋙ F.pf s.hom)
    (βrs : F.sh e.i ⟶ F.sh c.i ⋙ F.pf (r.comp s).hom)
    (hβ : ∀ K, βrs.app K = βs.app K ≫ (F.pf s.hom).map (βr.app K) ≫
      (F.pfComp' r.hom s.hom (r.comp s).hom
        (Compactification.Refinement.comp_hom r s).symm).inv.app ((F.sh c.i).obj K)) :
    refinement_transport F s βs ≫ refinement_transport F r βr =
      refinement_transport F (r.comp s) βrs := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, refinement_transport_app, Category.assoc]
  have hn := (F.pfComp' s.hom e.g d.g s.hom_g).inv.naturality (βr.app K)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [F.pfComp'_assoc_inv_app r.hom s.hom e.g (r.comp s).hom d.g c.g
    (Compactification.Refinement.comp_hom r s).symm s.hom_g (r.comp s).hom_g r.hom_g]
  rw [← (F.pf e.g).map_comp_assoc, ← (F.pf e.g).map_comp_assoc]
  simp only [Category.assoc]
  rw [← hβ]

private lemma normalization_cartesian
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 X) r.hom d.i)
    (N : EtaleCompactSupportNormalization A) :
    refinement_transport (unboundedFormalism A) r
      (unboundedEtaleRefinementOpenComparison A r N).hom =
        (unboundedFormalism A).refinementComparison r hr := by
  let : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  let : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  let hcL : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  let hcC : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  let : IsLocallyNoetherian (refinementOpenCompactification r).Z := hcL
  let : CompactSpace (refinementOpenCompactification r).Z := hcC
  let : IsNoetherian c.Z := ⟨⟩
  let : IsNoetherian d.Z := ⟨⟩
  let : IsNoetherian (refinementOpenCompactification r).Z := ⟨⟩
  let sq : CommSq c.i (𝟙 X) r.hom d.i := hr.toCommSq
  obtain ⟨θ, Γ, hθ, hΓ, hcart, _⟩ := unboundedProperOpenInterchange A
  let θ₀ := θ c.i (𝟙 X) r.hom d.i sq
  let Γ₀ := Γ c.i (𝟙 X) r.hom d.i sq
  have hβ := normalization_open_interchange A d.i (refinementOpenCompactification r)
    N θ₀ Γ₀ (hθ c.i (𝟙 X) r.hom d.i sq) (hΓ c.i (𝟙 X) r.hom d.i sq)
  obtain ⟨lam, hlam, hcartΓ⟩ := hcart c.i (𝟙 X) r.hom d.i hr
  have he : Γ₀.hom =
      openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} A) hr.flip := by
    apply NatTrans.ext
    funext K
    change (Γ c.i (𝟙 X) r.hom d.i hr.toCommSq).hom.app K = _
    rw [hcartΓ K]
    symm
    apply adjunct_eq_inverse
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) d.i)
      _ (lam.app K)
    have ht := unboundedEtaleCompactSupport_tower_adjunct A hr K
    change _ ≫ lam.hom.app K = _
    rw [hlam K]
    simp only [unboundedEtaleProperOpenRestriction, rightDerivedLowerStar, asIso_inv,
      NatIso.isIso_inv_app] at ht
    exact ht
  apply NatTrans.ext
  funext K
  rw [refinement_transport_app, CompactSupportFormalism.refinementComparison_app]
  have hβ' : (unboundedEtaleRefinementOpenComparison A r N).hom = _ := hβ
  rw [hβ', identity_prepend_app]
  rw [unbounded_pf_id, ← right_derived_identity_iso_eq
    (lowerStar (ModuleCat.{u + 1} A) (𝟙 X)) (lowerStarId (ModuleCat.{u + 1} A) X)]
  rw [unbounded_open_exchange A hr.flip]
  rw [he]
  rfl
private lemma comparison_inverse
    {C : Type*} [Category C] {X Y Z : C}
    (e : Y ≅ Z) (f : X ≅ Z) (t : X ⟶ Y) (h : t ≫ e.hom = f.hom) :
    e.inv = f.inv ≫ t := by
  apply (cancel_mono e.hom).1
  rw [Iso.inv_hom_id, Category.assoc, h, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma normalization_refinement_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} {c d e : Compactification f}
    (r : c.Refinement d) (s : d.Refinement e) (N : EtaleCompactSupportNormalization A)
    (K : DerivedCategoryModule A X) :
    (unboundedEtaleRefinementOpenComparison A (r.comp s) N).hom.app K =
      (unboundedEtaleRefinementOpenComparison A s N).hom.app K ≫
        (lowerStar (ModuleCat.{u + 1} A) s.hom).rightDerivedFunctor.map
          ((unboundedEtaleRefinementOpenComparison A r N).hom.app K) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) s.hom)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom s.hom (r.comp s).hom rfl)).hom.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) := by
  let : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
  let : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
  let hdL : IsLocallyNoetherian d.Z := LocallyOfFiniteType.isLocallyNoetherian d.g
  let hdC : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  let : IsLocallyNoetherian (refinementOpenCompactification s).Z := hdL
  let : CompactSpace (refinementOpenCompactification s).Z := hdC
  let ρ : (refinementOpenCompactification (r.comp s)).Refinement
      (refinementOpenCompactification s) :=
    { hom := r.hom, i_hom := r.i_hom, hom_g := rfl }
  have h := N.refinement e.i (refinementOpenCompactification (r.comp s))
    (refinementOpenCompactification s) ρ
  rw [← Category.assoc, ← Category.assoc] at h
  have hi := comparison_inverse
    (N.comparison e.i (refinementOpenCompactification (r.comp s)))
    (N.comparison e.i (refinementOpenCompactification s)) _ h
  have hK := congr_app hi K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp,  Category.assoc] at hK
  exact hK
private lemma normalization_transport_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (N : EtaleCompactSupportNormalization A) :
    refinement_transport (unboundedFormalism A) r
      (unboundedEtaleRefinementOpenComparison A r N).hom =
        ((unboundedFormalism A).shriekIso d c).hom := by
  let F := unboundedFormalism A
  let q : c.denseRefinement.Refinement c :=
    { hom := c.i.imageι
      i_hom := Scheme.Hom.toImage_imageι c.i
      hom_g := rfl }
  have hq := Compactification.Refinement.isPullback_denseRefinement c q
  have hqr := Compactification.Refinement.isPullback_denseRefinement c (q.comp r)
  have hcanq : F.refinementComparison q hq = (F.shriekIso c c.denseRefinement).hom := by
    rw [← F.shriekIso_symm c.denseRefinement c, F.shriekIso_eq_symm q hq]
    rfl
  have hcanqr : F.refinementComparison (q.comp r) hqr =
      (F.shriekIso d c.denseRefinement).hom := by
    rw [← F.shriekIso_symm c.denseRefinement d, F.shriekIso_eq_symm (q.comp r) hqr]
    rfl
  have htq := (normalization_cartesian A q hq N).trans hcanq
  have htqr := (normalization_cartesian A (q.comp r) hqr N).trans hcanqr
  have hcomp := refinement_transport_comp F q r
    (unboundedEtaleRefinementOpenComparison A q N).hom
    (unboundedEtaleRefinementOpenComparison A r N).hom
    (unboundedEtaleRefinementOpenComparison A (q.comp r) N).hom (fun K ↦ by
      rw [unbounded_pf_comp_inv]
      exact normalization_refinement_comp A q r N K)
  apply (cancel_mono (F.shriekIso c c.denseRefinement).hom).1
  calc
    refinement_transport F r (unboundedEtaleRefinementOpenComparison A r N).hom ≫
        (F.shriekIso c c.denseRefinement).hom =
      refinement_transport F r (unboundedEtaleRefinementOpenComparison A r N).hom ≫
        refinement_transport F q (unboundedEtaleRefinementOpenComparison A q N).hom := by
          rw [htq]
    _ = refinement_transport F (q.comp r)
        (unboundedEtaleRefinementOpenComparison A (q.comp r) N).hom := hcomp
    _ = (F.shriekIso d c.denseRefinement).hom := htqr
    _ = (F.shriekIso d c).hom ≫ (F.shriekIso c c.denseRefinement).hom :=
      (congrArg Iso.hom (F.shriekIso_trans d c c.denseRefinement)).symm

end NormalizationRefinements

/-- Every proper refinement, including a noncartesian one, gives the comparison normalized
as the identity on the source open. The graph-normalized open comparison is the identity
there; applying the ambient direct image and composing direct images gives this formula.
Source: Stacks Project, Tags 0F7I and 0F7B
(blueprint: lem-amb-unbounded-compact-support-comparisons).
Proof: sheaf normalization determines the comparison because its map to direct image is
monic. The prescribed injective model then identifies its derived map with proper/open
interchange. For a cartesian refinement, the specified adjunct identifies this with the
formalism comparison. Apply the normalization family's refinement law to the coarser open
to obtain composition for arbitrary refinements. The concrete dense refinement of the
source maps cartesianly to both compactifications. Composition and cancellation of its
isomorphism give the result for the original refinement. -/
theorem unboundedEtaleCompactSupport_refinement_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (N : EtaleCompactSupportNormalization A) :
    (rightDerivedLowerShriekOfCompactificationIso A d c).hom =
      Functor.whiskerRight (unboundedEtaleRefinementOpenComparison A r N).hom
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom := by
  have h := normalization_transport_eq A r N
  rw [unbounded_shriek_iso] at h
  rw [refinement_transport, unbounded_pf_comp_inv] at h
  exact h.symm

end AlgebraicGeometry.Etale
