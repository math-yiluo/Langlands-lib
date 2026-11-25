/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Normalized exact localization of fixed tensor

Source: Stacks Project, sites-cohomology.tex, Tag 06YU and its preceding construction;
categories.tex, Tags 04VG and 04VK; derived.tex, definition-distinguished-triangle.
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison)

The abbreviations expose the published resolving tensor and comparison, rather than choosing
new resolutions or a new tensor. `NormalizedDescent` packages the conclusions for one side.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Pretriangulated MonoidalCategory

namespace SheafOfModules.FixedTensorLocalization

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The recorded module-sheaf category. Source: Stacks, Modules on Sites, 03DA
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Unbounded complexes. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Complexes := CochainComplex (Modules R) ℤ

/-- The homotopy category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Homotopy := HomotopyCategory (Modules R) (.up ℤ)

/-- Quotient by chain homotopy. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev quotient := HomotopyCategory.quotient (Modules R) (.up ℤ)

/-- The direct-sum total tensor with its canonical signs. Source: Stacks, Tag 06YM
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev totalTensor :=
  let _ (I : Type r) : Limits.HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  show CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ from
  (@curriedTensor (Modules R) _ (SheafOfModules.monoidalCategory R)).map₂CochainComplex

variable [HasDerivedCategory.{w} (Modules R)]

/-- The chosen-universe derived category. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Derived := DerivedCategory (Modules R)

/-- Homotopy localization. Source: Stacks, Tag 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev Q := DerivedCategory.Qh (C := Modules R)

/-- The resolving full subcategory selected by the published descent theorem.
Source: Stacks, Tags 06YS and 06YU
(blueprint: lem-weil-pbc-fixed-tensor-localization-comparison). -/
abbrev resolving : ObjectProperty (Homotopy R) :=
  (site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0} J R).choose

end SheafOfModules.FixedTensorLocalization
