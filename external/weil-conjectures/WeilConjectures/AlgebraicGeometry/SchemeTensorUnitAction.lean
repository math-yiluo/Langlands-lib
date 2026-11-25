/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Tensor action on a complex through the single unit
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: def-pc-scheme-tensor-unit-action).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Tensor an actual chain evaluation into the single unit with F, then act on F.
Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DQ.
(blueprint: def-pc-scheme-tensor-unit-action).
The associator, tensor map and right unitor are the standard constructed complex
maps. Keeping this composite behind a definition avoids re-elaborating its large
coproduct instance terms in every evaluation statement. -/
@[irreducible]
def schemeTensorUnitAction (Y : Scheme.{u})
    (F V P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (e : pullbackTensorTotal Y V P ⟶
      (HomologicalComplex.single _ (.up ℤ) 0).obj
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))) :
    pullbackTensorTotal Y (pullbackTensorTotal Y F V) P ⟶ F := by
  letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  letI : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  exact (HomologicalComplex.associator F V P).hom ≫
    HomologicalComplex.mapBifunctorMap (𝟙 F) e (curriedTensor _) (.up ℤ) ≫
    (HomologicalComplex.rightUnitor F).hom

end AlgebraicGeometry
