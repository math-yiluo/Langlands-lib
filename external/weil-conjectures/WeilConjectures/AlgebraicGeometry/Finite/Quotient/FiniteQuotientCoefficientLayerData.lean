/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Explicit objects in the finite coefficient-layer triangle

The first object uses the actual kernel of the quotient of coefficient sheaves;
the last object is the restriction of the previous quotient complex.
Source: Stacks Project, Tag 0942.
(blueprint: def-weil-pbc-finite-quotient-coefficient-layer-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The actual quotient map, regarded as a map of rank-one coefficient modules.
Source: Stacks Project, Tag 0942.
(blueprint: def-weil-pbc-finite-quotient-coefficient-layer-data). -/
def finiteQuotientUnitMap (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    SheafOfModules.unit (completedAdicFiniteRing X d (n + 1)) ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)))).obj
        (SheafOfModules.unit (completedAdicFiniteRing X d n)) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat.{t + 1} AddCommGrpCat.{t + 1}).map
      (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))).hom.app U))
    (fun r ↦ by
      ext m
      exact ((((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
          (completedAdicQuotientCommMap X d (n + 1) n
            (Nat.le_succ n))).hom.app U).hom.map_mul r m).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom
      (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))).hom.naturality f) _

/-- Tensor the successor reduction with the actual kernel of the quotient map.
The kernel, not a chosen witness of existence, defines the coefficient layer.
Source: Stacks Project, Tag 0942.
(blueprint: def-weil-pbc-finite-quotient-coefficient-layer-data). -/
def finiteQuotientLayerObject (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (M : DerivedCategory (CompletedAdicModules X d))
    (n : ℕ) : DerivedCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
  letI : EssentiallySmall.{t + 1} X.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  (SheafOfModules.siteDerivedTensorIndependentCoefficients (ProEt.topology X)
    (completedAdicFiniteCommRing X d (n + 1))).obj
    ((completedAdicQuotientReduction X d (n + 1)).obj M,
      (DerivedCategory.singleFunctor _ 0).obj (kernel (finiteQuotientUnitMap X d n)))

/-- The previous derived quotient regarded over the successor coefficient ring.
Restriction is performed on the canonical complex representative of the localization.
Source: Stacks Project, Tag 0942.
(blueprint: def-weil-pbc-finite-quotient-coefficient-layer-data). -/
def finiteQuotientPreviousObject (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (M : DerivedCategory (CompletedAdicModules X d))
    (n : ℕ) : DerivedCategory (SheafOfModules.{t + 1}
      (completedAdicFiniteRing X d (n + 1))) :=
  let F := SheafOfModules.restrictScalars.{t + 1}
    ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)))
  DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
    (DerivedCategory.Q.objPreimage ((completedAdicQuotientReduction X d n).obj M)))

end AlgebraicGeometry.Scheme
