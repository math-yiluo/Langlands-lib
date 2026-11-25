/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
import all WeilConjectures.AlgebraicGeometry.Compactification.CompactificationProjectionExchangeCoherence

/-! # Tensor compatibility of derived inverse-image composition

The theorem is an intermediate result: it identifies the two canonical routes
from a derived tensor through two successive inverse images. Its proof uses the
monoidal comparison of the left-derived inverse image, naturality, and the
composition coherence of derived inverse-image functors.

## References

* Stacks 07A4 and 03EL
* Stacks Project, Tag 0F7B
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem pullComp_eq
    (V₀ : Type*) [Category.{u + 1} V₀] [Abelian V₀]
    [IsGrothendieckAbelian.{u + 1} V₀] [MonoidalCategory V₀]
    [MonoidalPreadditive V₀] [SymmetricCategory V₀] [MonoidalClosed V₀]
    [Abelian.HasFunctorialFlatResolution V₀]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X) :
    leftDerivedUpperStarComp V₀ s b =
      (upperStar V₀ (s ≫ b)).leftDerivedFunctorNatIso (upperStarComp V₀ s b) ≪≫
        (upperStar V₀ b).leftDerivedFunctorCompIso (upperStar V₀ s) := by
  rfl

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

attribute [local instance 30000] isNoetherian_of_finite
  AlgebraicGeometry.ProEtale.preservesHomology_upperStar
  AlgebraicGeometry.ProEtale.preservesFiniteLimits_upperStar
  AlgebraicGeometry.ProEtale.additive_upperStar
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.hasDerivedMonoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Adjunction.derivedAdjunction
attribute [local irreducible] leftDerivedUpperStarComp upperStar lowerStar
  Functor.leftDerivedTensorComparison Functor.leftDerivedFunctorCounit
  Functor.leftDerivedFunctorNatIso Functor.leftDerivedFunctorCompIso
  leftDerivedUpperStarTensorComparison leftDerivedUpperStarTensorIso
  leftDerivedUpperStarTensorNatIso

private theorem uncurryTensor_map
    {C₀ : Type*} [Category C₀] [MonoidalCategory C₀]
    {X₁ X₂ Y₁ Y₂ : C₀} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (Functor.uncurry.obj (curriedTensor C₀)).map (Prod.mkHom f g) = f ⊗ₘ g := by
  simpa only [Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map]
    using (tensorHom_def f g).symm

section Generic
universe u₁ u₂ u₃
variable {C : Type u₁} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [MonoidalClosed C] [BraidedCategory C] [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalPreadditive D]
  [MonoidalClosed D] [BraidedCategory D] [HasFunctorialFlatResolution D]
  {E : Type u₃} [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [MonoidalClosed E] [BraidedCategory E] [HasFunctorialFlatResolution E]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesFlat] [G.IsLeftAdjoint] [G.Monoidal]
  (H : C ⥤ E) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesFlat] [H.IsLeftAdjoint] [H.Monoidal]

private theorem derived_compositor_tensor (e : H ≅ F ⋙ G)
    [NatTrans.IsMonoidal e.hom] (M N : DerivedCategory C) :
    let c := H.leftDerivedFunctorNatIso e ≪≫ F.leftDerivedFunctorCompIso G
    c.hom.app (((curriedTensor (DerivedCategory C)).obj M).obj N) ≫
      G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app M).app N) ≫
      (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj M)).app
        (F.leftDerivedFunctor.obj N) =
    (H.leftDerivedTensorComparison.app M).app N ≫
      (Functor.uncurry.obj (curriedTensor (DerivedCategory E))).map
        (Prod.mkHom (c.hom.app M) (c.hom.app N)) := by
  intro c
  rw [uncurryTensor_map]
  simp only [curriedTensor_obj_obj]
  dsimp only [c, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_leftDerivedTensorComparison_app_app_comp]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.leftDerivedTensorComparison_naturality_app_assoc]
  rw [tensorHom_comp_tensorHom]

end Generic

private theorem pullTensor_hom_eq
    (V₀ : Type*) [Category.{u + 1} V₀] [Abelian V₀]
    [IsGrothendieckAbelian.{u + 1} V₀] [MonoidalCategory V₀]
    [MonoidalPreadditive V₀] [SymmetricCategory V₀] [MonoidalClosed V₀]
    [Abelian.HasFunctorialFlatResolution V₀] [UpperStarPreservesFlat V₀]
    {U X : Scheme.{u}} (f : U ⟶ X)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V₀)) :
    (leftDerivedUpperStarTensorIso V₀ f M N).hom =
      ((upperStar V₀ f).leftDerivedTensorComparison.app M).app N := by
  rw [leftDerivedUpperStarTensorIso_hom,
    leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison]

/-- Canonical derived inverse-image composition preserves the tensor comparison. -/
theorem properOpenPullTensorComposition
    (V₀ : Type*) [Category.{u + 1} V₀] [Abelian V₀]
    [IsGrothendieckAbelian.{u + 1} V₀] [MonoidalCategory V₀]
    [MonoidalPreadditive V₀] [SymmetricCategory V₀] [MonoidalClosed V₀]
    [Abelian.HasFunctorialFlatResolution V₀] [UpperStarPreservesFlat V₀]
    {U V X : Scheme.{u}} (s : U ⟶ V) (b : V ⟶ X)
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) V₀)) :
    (leftDerivedUpperStarComp (V₀) s b).hom.app
        (((derivedTensor V₀ X).obj M).obj N) ≫
      ((upperStar V₀ s).leftDerivedFunctor).map (leftDerivedUpperStarTensorIso
        (V₀) b M N).hom ≫
      (leftDerivedUpperStarTensorIso (V₀) s
        (((upperStar V₀ b).leftDerivedFunctor).obj M)
        (((upperStar V₀ b).leftDerivedFunctor).obj N)).hom =
    (leftDerivedUpperStarTensorIso (V₀) (s ≫ b) M N).hom ≫
      (Functor.uncurry.obj (derivedTensor V₀ U)).map
        (Prod.mkHom
          ((leftDerivedUpperStarComp (V₀) s b).hom.app M)
          ((leftDerivedUpperStarComp (V₀) s b).hom.app N)) := by
  have := comp_monoidal V₀ s b
  simp only [pullTensor_hom_eq]
  rw [pullComp_eq]
  dsimp only [derivedTensor]
  exact derived_compositor_tensor (upperStar V₀ b) (upperStar V₀ s)
    (upperStar V₀ (s ≫ b)) (upperStarComp V₀ s b) M N

attribute [instance] CategoryTheory.sheafToPresheaf_isRightAdjoint

end AlgebraicGeometry.ProEtale
