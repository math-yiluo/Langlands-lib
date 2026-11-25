/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo

/-! # Ordinary-module presentation of derived change of rings

Source: Stacks Project, Tags 06YY, 06XN, 06Y1 and 0A6A.
(blueprint: lem-pur-derived-change-of-rings).
The generic ringed-site construction remains publicly imported. The additional
presentation retains ordinary module complexes and normalizes the tensor comparison
by the ordinary scalar-extension tensor comparison on K-flat representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat


-- A full, essentially surjective functor is initial: every comma object maps
-- to a fixed lift of the target, giving a zigzag between any two objects.
section LocalizationTensor

universe v w
variable {A : Type*} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

end LocalizationTensor

section UniversalPair

universe v w
variable {A B : Type*} [Category.{v} A] [Category.{w} B] [Abelian A] [Abelian B]
  [IsGrothendieckAbelian.{v} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [MonoidalClosed A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
  [HasColimitsOfSize.{0, 0} A]

end UniversalPair

end ModuleCat

namespace ModuleCat

/-- The ordinary-module universal pair, including its canonical tensor structure.
Source: Stacks 06YY and 0A6A (blueprint: lem-pur-derived-change-of-rings).
The tensor equation fixes the structure on resolving representatives, so the
monoidal structure is not arbitrary extra data. -/
structure OrdinaryDerivedChangeOfRings {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) where
  F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S)
  counit : DerivedCategory.Q ⋙ F ⟶
    (extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : F.IsLeftDerivedFunctor counit
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  pointwise : ((extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))
  computes : ∀ P : CochainComplex (ModuleCat.{u} R) ℤ,
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
      IsIso (counit.app P)
  triangulated : ∃ (_ : F.CommShift ℤ), F.IsTriangulated
  [monoidal : F.Monoidal]
  unit_normalized :
    F.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
        counit.app (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ≫
        DerivedCategory.Q.map (Functor.OplaxMonoidal.η
          ((extendScalars φ).mapHomologicalComplex (.up ℤ))) =
      Functor.OplaxMonoidal.η F ≫ Functor.LaxMonoidal.ε DerivedCategory.Q
  tensor_normalized : ∀ (P Q : CochainComplex (ModuleCat.{u} R) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q →
    Functor.LaxMonoidal.μ F (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        F.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫ counit.app (P ⊗ Q) ≫
        DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
            (extendScalars φ)).app P).app Q) =
      (counit.app P ⊗ₘ counit.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)
          (((extendScalars φ).mapHomologicalComplex (.up ℤ)).obj Q)

end ModuleCat
