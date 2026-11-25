/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Canonical data for ordered integration and adjoint transposition
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale.IntegrationComposition

/-- Unit identification for an arbitrary coefficient category, packaged before specialization.
-/
@[irreducible]
def integrationUnitObjectIso
    (B : Type*) [Category.{u + 1} B] [Abelian B] [IsGrothendieckAbelian.{u + 1} B]
    [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B] [UpperStarPreservesFlat B]
    {V T : Scheme.{u}} (f : V ⟶ T)
    (W : _root_.DerivedCategory (Sheaf V.smallEtaleTopology B)) :
    ((derivedTensor B V).obj ((upperStar B f).mapDerivedCategory.obj (𝟙_ _))).obj W ≅ W :=
  ((derivedTensor B V).mapIso
    ((leftDerivedUpperStarIsoMapDerivedCategory B f).symm.app _ ≪≫
      leftDerivedUpperStarUnitIso B f)).app W ≪≫ derivedTensorLeftUnitor B V W

variable {A : Type (u + 1)} [CommRing A] {X Y Z : Scheme.{u}}

/-- The tensor-twisted exact inverse image appearing in integration. -/
def object (f : X ⟶ Y) (W : DerivedCategoryModule A X)
    (K : DerivedCategoryModule A Y) : DerivedCategoryModule A X :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj W

/-- Integration: inverse canonical projection, tensor the trace, then the unit constraint. -/
def integration (f : X ⟶ Y) [HasCompactification f]
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj (object f W K) ⟶ K :=
  @inv _ _ _ _ (compactSupportProjectionMap A f W K) (hP K) ≫
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map t ≫
    (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y K).hom

/-- The transpose under the specified actual right adjoint, with no constructibility bound. -/
def gamma (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K))
    (K : DerivedCategoryModule A Y) : object f W K ⟶ R.obj K :=
  adj.homEquiv _ _ (integration f W t hP K)

/-- The exact inverse-image unit constraint, transported through the canonical comparison. -/
def unitObjectIso (f : X ⟶ Y) (W : DerivedCategoryModule A X) :
    object f W (𝟙_ (DerivedCategoryModule A Y)) ≅ W :=
  integrationUnitObjectIso (ModuleCat.{u + 1} A) f W

/-- Orientation at the unit, whose domain is W after the canonical unit identification. -/
def orientation (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (W : DerivedCategoryModule A X)
    (t : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj W ⟶
      𝟙_ (DerivedCategoryModule A Y))
    (hP : ∀ K : DerivedCategoryModule A Y, IsIso (compactSupportProjectionMap A f W K)) :
    W ⟶ R.obj (𝟙_ (DerivedCategoryModule A Y)) :=
  (unitObjectIso f W).inv ≫ gamma f R adj W t hP _

/-- The dualizing tensor map, defined wherever its canonical projection is invertible. -/
def theta (f : X ⟶ Y) [HasCompactification f]
    (R : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣ R)
    (L : DerivedCategoryModule A Y)
    (hP : IsIso (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L)) :
    object f (R.obj (𝟙_ _)) L ⟶ R.obj L :=
  adj.homEquiv _ _
    (@inv _ _ _ _ (compactSupportProjectionMap A f (R.obj (𝟙_ _)) L) hP ≫
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj L).map (adj.counit.app (𝟙_ _)) ≫
      (derivedTensorRightUnitor (ModuleCat.{u + 1} A) Y L).hom)

/-- Exact pullback of tensor, using the K-flat tensor comparison and exact descent. -/
def pullTensorIso (f : X ⟶ Y) (K M : DerivedCategoryModule A Y) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
      (((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj M) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj M) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm.app _ ≪≫
    leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f K M ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app K)).app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).obj _).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app M)

/-- Ordered reassociation a_K, with exact pullback composition and no block interchange. -/
def reassociation (f : X ⟶ Y) (g : Y ⟶ Z)
    (Wf : DerivedCategoryModule A X) (Wg : DerivedCategoryModule A Y)
    (K : DerivedCategoryModule A Z) :
    object (f ≫ g) (object f Wf Wg) K ≅ object f Wf (object g Wg K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      ((unboundedEtaleUpperStarCompIso A f g).app K)).app _ ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} A) X _ _ Wf).symm ≪≫
    ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso
      (pullTensorIso f
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) Wg).symm).app Wf

end AlgebraicGeometry.Etale.IntegrationComposition
