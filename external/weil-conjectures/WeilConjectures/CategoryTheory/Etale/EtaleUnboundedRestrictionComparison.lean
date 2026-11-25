/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Ambient derived restriction comparisons for the bounded-below interface

Source: Stacks Project, Tags 03FD, 0D6J and 07A4
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons).
The original bounded-below isomorphisms are reexported. These definitions give
canonical ambient maps whose restrictions to D+ are those comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory.Functor

/-- The restriction square transported through two specified geometric comparisons.
Source: Stacks 07A4 (blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons). -/
def exactDerivedComparisonSquare
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F₁ : B ⥤ A) (F₂ : A ⥤ E) (G₁ : B ⥤ D) (G₂ : D ⥤ E)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (L : DerivedCategory A ⥤ DerivedCategory E)
    (M : DerivedCategory B ⥤ DerivedCategory D)
    (ε : L ≅ F₂.mapDerivedCategory) (δ : M ≅ G₁.mapDerivedCategory) :
    F₁.mapDerivedCategory ⋙ L ≅ M ⋙ G₂.mapDerivedCategory :=
  Functor.isoWhiskerLeft F₁.mapDerivedCategory ε ≪≫
    Functor.mapDerivedCategorySquareIso e ≪≫
    Functor.isoWhiskerRight δ.symm G₂.mapDerivedCategory

/-- An exact geometric representative in the specified derived comparison.
Source: Stacks 07A4 (blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons). -/
def exactDerivedRepresentative
    {A E : Type*} [Category A] [Category E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DerivedCategory A ⥤ DerivedCategory E) (ε : L ≅ F.mapDerivedCategory)
    (P : CochainComplex A ℤ) :
    L.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  ε.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Exact inverse-image/restriction comparison on the ambient derived categories.
Source: Stacks 07A4 and 0D6J
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons). -/
def scalarRestrictionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⋙
        L(upperStar (ModuleCat.{u + 1} A) f) ≅
      L(upperStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _

/-- The ambient direct-image comparison, as the mate of the exact inverse-image square.
On D+ its counit normalization is the recorded canonical bounded-below comparison.
Source: Stacks 0D6J and 07A4
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons). -/
def scalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    R(lowerStar (ModuleCat.{u + 1} B) f) ⋙
        Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ ⋙
        R(lowerStar (ModuleCat.{u + 1} A) f) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (scalarRestrictionPullbackIso φ f).hom

end AlgebraicGeometry.Etale
