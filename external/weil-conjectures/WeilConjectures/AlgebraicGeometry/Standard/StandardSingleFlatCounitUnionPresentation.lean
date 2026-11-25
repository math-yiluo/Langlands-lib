/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnionCore
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitUnionEquation

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The presentation for one module on a union is obtained from presentations on
the two opens and their overlap.  This is the per-module Mayer--Vietoris gluing
step in the proof of `standardSingleFlatCounitOnOpen_union`.
(blueprint: lem-pc-standard-single-flat-counit-union-presentation).

Source: Stacks Project, Tag 0DJ9, relative Mayer--Vietoris induction step.
The proof forms the shifted cone of the restriction-difference map between the
three bounded flat presentations, lifts that map over the affine base, and uses
naturality of the counit and the Mayer--Vietoris triangle.  Finite sums and
cones preserve boundedness and termwise flatness; the resulting cone supplies
the required presentation and its canonical counit equation. -/
theorem standardSingleFlatCounitPresentation_union_of_open_presentations
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    StandardSingleFlatCounitPresentation ((U ⊔ V).ι ≫ p) N g := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let := HasDerivedCategory.standard A.Modules
  let := HasDerivedCategory.standard B.Modules
  rcases standardSingleFlatCounitUnionCore p g U V N hN hPU hPV hPUV with
    ⟨K, hbounded, hflat, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := standardSingleFlatCounitUnionEquation p g U V N hN hPU hPV hPUV K
    hbounded hflat e
  exact ⟨K, hbounded, hflat, e, t, ht⟩

end AlgebraicGeometry
