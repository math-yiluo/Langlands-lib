/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
public import WeilConjectures.Algebra.Homology.PullbackTensorCanonical.PullbackTensorCanonicalShiftUnit
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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

/-! # Comparing the two presentations of normalized tensor models

Source: Stacks 07A4, 0G7E and 03EL. These are explicit identifications of the
ordinary comparison, its single-complex unit and the recorded K-flat tensor model.
(blueprint: lem-pur-finite-derived-tensor-model-bridge).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open CategoryTheory.CochainPullback CategoryTheory.RingedDerivedComparisons
open WeilConjectures

attribute [-instance] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 100000] HomologicalComplex.monoidalCategoryStruct
attribute [local irreducible] CommRingCat.hasForgetToRingCat sheafCompose
  CommRingCat.instConcreteCategoryRingHomCarrier RingCat.instConcreteCategoryRingHomCarrier
  SheafOfModules.monoidalCategory SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive SheafOfModules.siteSheafTensorRight
  DerivedCategory instCategoryDerivedCategory
  HomologicalComplex₂.total CategoryTheory.CochainPullback.comparison
  HomologicalComplex.single

namespace CategoryTheory.FiniteDerivedTensorModels

/-- The ordinary comparison with its identical insertion and tensor maps.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
def legacyComparison {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f) :
    SheafOfModules.CanonicalRingedTensorComparison Y.A X.A f.RI f.uInv f.I
      f.coefficient f.L f.hobj where
  q := k.q
  q_one := k.q_one
  mu := k.mu
  naturality := k.naturality
  pure := k.pure

section LegacyUnit
attribute [local semireducible] SheafOfModules.monoidalCategory

/-- The ordinary normalized unit has the specified single-complex comparison.
Source: Stacks 07A4, 0G7E and 03EL.
(blueprint: lem-pur-finite-derived-tensor-model-bridge). -/
theorem unit_presentation {X Y : Site.{u, w}}
    (f : RingedPullback.{u, u, u, u, u} Y.A X.A) (k : Comparison f) :
    ∃ j : f.L.obj (SheafOfModules.unit Y.ring) ≅ SheafOfModules.unit X.ring,
      (∀ M : Y.modules,
        ((legacyComparison f k).mu M (SheafOfModules.unit Y.ring)).hom ≫
            (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
            ((SheafOfModules.monoidalCategory X.A).rightUnitor (f.L.obj M)).hom =
          f.L.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
      (HomologicalComplex.singleMapHomologicalComplex f.L (.up ℤ) 0).hom.app
          (SheafOfModules.unit Y.ring) ≫
        (CochainComplex.singleFunctor X.modules 0).map j.hom = (unit f k).hom := by
  refine ⟨moduleUnit f k, ?_, ?_⟩
  · exact (Classical.choose_spec
      (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
        Y.A X.A f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)).1
  · rfl

end LegacyUnit

end CategoryTheory.FiniteDerivedTensorModels
