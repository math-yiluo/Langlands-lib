/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.ResolvingTensorSigned.ResolvingTensorSignedCoherence
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Exact pullback and the normalized signed derived tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 06YS, 0G7E and 07A4;
sites-modules.tex, Tags 05VD and 03EL; derived.tex, Tag 015F;
more-algebra.tex, Tags 0FNG and 0FNH.
(blueprint: lem-pur-exact-pullback-signed-comparison).

The tensor and its representative isomorphisms are the published K-flat descent.
The helper structure records just the normalized associativity and symmetry maps
mentioned in the statement, on that same tensor; it does not choose another tensor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD r wR wS

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.CochainPullback hiding Modules
open SheafOfModules.KFlatFixedTensor
open SheafOfModules.PullbackTensorCanonical

namespace SheafOfModules.ExactPullbackSigned

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso
attribute [local irreducible] IsNormalized HasCanonicalTensorShifts
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{wR} (Modules R)]

local instance (priority := 20000) : J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
  inferInstance

/-- Evaluation of the existing K-flat-derived tensor, without changing its data.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
abbrev tensor (A B : DerivedCategory (Modules R)) := ((derivedTensor R).obj A).obj B

/-- The existing derived bifunctor applied to a pair of morphisms.
Source: Stacks 06YU (blueprint: lem-pur-exact-pullback-signed-comparison). -/
def tensorMap {A A' B B' : DerivedCategory (Modules R)} (a : A ⟶ A') (b : B ⟶ B') :
    tensor R A B ⟶ tensor R A' B' :=
  (Functor.uncurry.obj (derivedTensor R)).map (Prod.mkHom a b)

attribute [local irreducible] tensorMap

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local instance 2000] SheafOfModules.KFlatFixedTensor.tensorAdditive
  SheafOfModules.KFlatFixedTensor.tensorObjAdditive
  SheafOfModules.KFlatFixedTensor.tensorHasMapBifunctor
attribute [local instance 2000] HomologicalComplex.monoidalCategoryStruct
  HomologicalComplex.monoidalCategory SheafOfModules.cochainModulesMonoidal
attribute [local instance 4001] DerivedTensorConstraints.complexMonoidal
  DerivedTensorConstraints.complexMonoidalStruct
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  Functor.mapHomologicalComplex Functor.mapBifunctorHomologicalComplex HomologicalComplex₂.total
  CochainComplex.Monoidal.braiding

attribute [local irreducible] IsFlatOnSite CochainComplex.IsKFlatIndependentCoefficients

variable {R}
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {S : Sheaf K CommRingCat.{r}}
  [HasDerivedCategory.{wS} (Modules S)]
  (f : RingedPullback.{r, uC, vC, uD, vD} R S)
  (k : Comparison.{r, uC, vC, uD, vD} f)
  [PreservesFiniteLimits f.L] [PreservesFiniteColimits f.L]

local instance (priority := 20000) : K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) :=
  inferInstance

variable (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
  (epsilon : DerivedCategory.Q ⋙ L ⟶ pull.{r, uC, vC, uD, vD} f ⋙ DerivedCategory.Q)

end SheafOfModules.ExactPullbackSigned
