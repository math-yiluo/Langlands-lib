/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Scalar realization for an arbitrary commutative condensed ring

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Definition 3.5
and formula (3.1) (blueprint: def-zl-condensed-scalar-realization).
The scalar map is the constant-sheaf adjunction counit on the point. Derived extension
uses the universal K-flat construction, then the section-module equivalence and p_X^*.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The reconstructed ring sheaf has the original sections, restrictions and multiplication.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
abbrev condensedSectionRing :=
  InternalAbelianSheafModule.sectionRingSheaf (coherentTopology Profinite.{u}) Λ

/-- The underlying scalar ring Γ(*,Λ), with the multiplication inherited from Λ.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
abbrev condensedScalarRing : CommRingCat.{u + 1} :=
  (condensedSectionRing Λ).obj.obj (op (⊤_ Profinite.{u}))

/-- The canonical constant-section map, the counit of constant sheaf versus sections at *.
Source: HRS, Definition 3.5 (blueprint: def-zl-condensed-scalar-realization). -/
def condensedScalarMap :
    realizationRing (coherentTopology Profinite.{u}) (condensedScalarRing Λ) ⟶
      condensedSectionRing Λ :=
  (constantSheafAdj (coherentTopology Profinite.{u}) CommRingCat.{u + 1}
    terminalIsTerminal).counit.app (condensedSectionRing Λ)

/-- The standard localization size for constant scalar module sheaves.
Source: Stacks 05RU (blueprint: def-zl-condensed-scalar-realization). -/
instance condensedScalarConstantHasDerived :
    HasDerivedCategory.{u + 2}
      (realizationModules (coherentTopology Profinite.{u}) (condensedScalarRing Λ)) :=
  HasDerivedCategory.standard _

/-- The standard localization size for sectionwise condensed module sheaves.
Source: Stacks 05RU (blueprint: def-zl-condensed-scalar-realization). -/
instance condensedScalarSectionHasDerived :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1}
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (condensedSectionRing Λ))) :=
  HasDerivedCategory.standard _

/-- The derived coefficient extension, fixed by its universal counit and K-flat computation.
Its universal property determines the selected object up to counit-compatible isomorphism.
Source: HRS, formula (3.1), and Stacks 06YY
(blueprint: def-zl-condensed-scalar-realization). -/
def condensedScalarExtensionModel :
    SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (condensedScalarMap Λ) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (condensedScalarMap Λ))

end AlgebraicGeometry.ProEtale
