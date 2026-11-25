/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomologyPresentation
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
/-! # The source-only localized affine comparison

Source: Stacks Project, Tag 0DJ8, equation-bc.
(blueprint: def-pc-affine-base-change-into-pullback).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The localized comparison ending in stalks of the pullback cohomology sheaf,
before any morphism from that pullback is applied. Source: Stacks, Tag 0DJ8.
(blueprint: def-pc-affine-base-change-into-pullback). -/
def affineBaseChangeIntoPullback
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (K : schemeDerivedCategory X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (e : DerivedCategory.Q.obj P ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit g').app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) (p : X') (i : ℤ) :
    letI := SingleComplexBaseChange.leftAlgebra f g' p
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
    (ModuleCat.extendScalars (algebraMap
      (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
        SingleComplexBaseChange.B f' p) (SingleComplexBaseChange.C p))).obj
          ((SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).cohomology i) ⟶
      (RingedSpace.moduleStalkFunctor X'.toRingedSpace p).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i).obj
            ((derivedPullback g').obj K)) :=
  letI := SingleComplexBaseChange.leftAlgebra f g' p
  letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
  letI := hc
  let T := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor X'.toRingedSpace p
  (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i ≫
    HomologicalComplex.homologyMap
      (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i ≫
    (affineRepresentativeStalkIso X' p T i).inv ≫
    s.map (H.map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (moduleRings X'.toRingedSpace))).inv.app T ≫
      inv ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (derivedPullback g').map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))).hom.app P ≫ e.hom)))

end AlgebraicGeometry
