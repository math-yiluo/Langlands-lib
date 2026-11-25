/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Ordinary evaluation on the open scheme's actual site
Source: Stacks Project, Tags 08DJ and 08DQ, representative evaluation calculation.
(blueprint: def-pc-scheme-ordinary-evaluation-formula).
The existing local predicate has an over-site carrier. This predicate writes the
same component equation directly on a scheme's opens, so that transport can be
separated from the derived calculation. All complexes and components are actual
constructions; no comparison object is selected from an existence theorem.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- The ordinary component equation on the scheme site (rather than an over-site).
Source: Stacks Project, Tags 08DJ and 08DQ.
(blueprint: def-pc-scheme-ordinary-evaluation-formula). -/
def IsSchemeOrdinaryEvaluation (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F) : Prop :=
  letI := SheafOfModules.monoidalCategory Y.sheaf
  letI := SheafOfModules.symmetricCategory Y.sheaf
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let D := homComplex (R := Y.sheaf) P O
  let π := Classical.choose (homComplex_projections_exists (R := Y.sheaf))
  ∀ (p q n r : ℤ) (hpq : p + q = n),
    HomologicalComplex.ιMapBifunctor F D (curriedTensor _) (.up ℤ) p q n hpq ≫
      f.f n ≫ π P F n r (r + n) rfl =
    if h : r + q = 0 then
      SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) _ _
        ((β_ (P.X r) (F.X p ⊗ D.X q)).hom ≫
          (α_ (F.X p) (D.X q) (P.X r)).hom ≫
          F.X p ◁ ((β_ (D.X q) (P.X r)).hom ≫
            (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) _
              (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).symm
              (π P O q r 0 h ≫
                SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r))
                  (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom)) ≫
          (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = r + n)).hom)
    else 0

end AlgebraicGeometry
