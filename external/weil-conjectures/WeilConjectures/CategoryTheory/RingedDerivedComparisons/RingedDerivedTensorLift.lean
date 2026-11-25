/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedTensorDiagrams

/-! # Symmetric monoidal coherence of the canonical derived tensor comparison

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-lift).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

/-- The tensor and action-unit portion of a lift, with specified representative models.
Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-sfb-ringed-derived-tensor-lift). -/
structure TensorLift {X Y : Site.{u, w}} (e : RingedTensorEdge Y.corner X.corner)
    (rY : RingedTensorModel Y.corner) (rX : RingedTensorModel X.corner) where
  monoidal : @Functor.CoreMonoidal Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal e.left
  tensor_canonical : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      e.left monoidal U V).inv =
      (e.tensorComparison rY rX).hom.app (U, V)
  unit_canonical : ∃ j : e.pullback.obj (SheafOfModules.unit Y.ring) ≅
      SheafOfModules.unit X.ring,
    (∀ M : Y.modules,
      (e.ordinaryTensor.mu M (SheafOfModules.unit Y.ring)).hom ≫
          (SheafOfModules.monoidalCategory X.A).tensorHom (𝟙 _) j.hom ≫
          ((SheafOfModules.monoidalCategory X.A).rightUnitor (e.pullback.obj M)).hom =
        e.pullback.map ((SheafOfModules.monoidalCategory Y.A).rightUnitor M).hom) ∧
    e.left.map Y.coherence.unitIso.hom ≫
        derivedPullbackComplexComparison e.pullback e.left e.epsilon
          (ringedTensorUnitComplex.{u, u, u} Y.J Y.A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            e.pullback (ComplexShape.up ℤ) 0).hom.app (SheafOfModules.unit Y.ring) ≫
            (CochainComplex.singleFunctor X.modules 0).map j.hom) ≫
        X.coherence.unitIso.inv =
        (@Functor.CoreMonoidal.εIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          e.left monoidal).inv
  symmetric : ∀ U V : Y.D,
    (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
      e.left monoidal U V).inv ≫
        (X.symmetry.toBraidedCategory.braiding (e.left.obj U) (e.left.obj V)).hom =
      e.left.map (Y.symmetry.toBraidedCategory.braiding U V).hom ≫
        (@Functor.CoreMonoidal.μIso Y.D _ Y.closed.monoidal X.D _ X.closed.monoidal
          e.left monoidal V U).inv

end CategoryTheory.RingedDerivedComparisons
