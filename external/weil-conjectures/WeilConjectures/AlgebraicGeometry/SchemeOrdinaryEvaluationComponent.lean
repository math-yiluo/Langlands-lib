/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula

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

/-- A single scheme-site ordinary evaluation component, with its actual tensor-Hom map.
Source: Stacks Project, Tags 08DJ and 08DQ.
(blueprint: def-pc-scheme-ordinary-evaluation-component).
This is the same component formula as `IsSchemeOrdinaryEvaluation`, isolated
so that proofs can use the predicate without expanding its large tensor-Hom term. -/
def schemeOrdinaryEvaluationComponent (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (p q n r : ℤ) (hpq : p + q = n) :=
  letI := SheafOfModules.monoidalCategory Y.sheaf
  letI := SheafOfModules.symmetricCategory Y.sheaf
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let D := homComplex (R := Y.sheaf) P O
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
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


attribute [local irreducible] homComplexFunctor


/-- Component criterion for scheme ordinary evaluation.
Source: Stacks Project, Tags 08DJ and 08DQ.
(blueprint: lem-pc-scheme-ordinary-evaluation-of-components).
Proof: unfold the predicate and the isolated component formula; they give
exactly the same equation for every summand and projection. -/
theorem schemeOrdinaryEvaluation_of_components (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F) :
    (
  letI := SheafOfModules.monoidalCategory Y.sheaf
  letI := SheafOfModules.symmetricCategory Y.sheaf
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let D := homComplex (R := Y.sheaf) P O
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
  ∀ (p q n r : ℤ) (hpq : p + q = n),
    HomologicalComplex.ιMapBifunctor F D (curriedTensor _) (.up ℤ) p q n hpq ≫
      f.f n ≫ π P F n r (r + n) rfl =
    schemeOrdinaryEvaluationComponent Y P F p q n r hpq
) → IsSchemeOrdinaryEvaluation Y P F f := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    intro h
    unfold IsSchemeOrdinaryEvaluation
    unfold schemeOrdinaryEvaluationComponent at h
    exact h

end AlgebraicGeometry
