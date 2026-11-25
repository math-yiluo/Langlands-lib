/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential

import WeilConjectures.AlgebraicGeometry.SchemeTensorHomUncurrySummandNaturality
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationUncurriedComponent

/-! # Uncurrying ordinary evaluation on a triple summand
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Uncurrying the ordinary evaluation equation on one triple tensor summand.
Source: Stacks Project, cohomology.tex, Tags 08DJ and 08DQ;
ordinary evaluation chain calculation, step 3.
(blueprint: lem-pc-scheme-ordinary-evaluation-triple-component).

Proof: First restrict schemeTensorHomUncurry to the outer tensor summand using
schemeTensorHomUncurry_component. Naturality of the Hom projections under
eta_F and naturality of tensorHomEquiv move eta_F to the end of this map.
Naturality in the source tensor inclusion then expresses the remaining map
as the inverse tensorHomEquiv applied to the ordinary component equation hf.
For r+q=0, apply hf, cancel the tensorHomEquiv inverse with tensorHomEquiv,
and cancel the two symmetries. The remaining map is exactly the associator,
the dual Hom projection (identified with the tensor unit by singleObjXSelf),
and the right unitor displayed below. For r+q nonzero hf gives zero; the
additive tensor-Hom equivalence and composition send zero to zero. The
reindexing equality p=k follows from the two degree sums and r+q=0.
This calculation uses no putative evaluation map e and no factorization
hypothesis. It holds in negative degrees, for unbounded or zero complexes,
and for the empty scheme. -/
theorem schemeOrdinaryEvaluation_triple_component (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f)
    (p q r n k : ℤ) (hpq : p + q = n) (hnr : n + r = k) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf))
    (HomologicalComplex.ιMapBifunctor F V (curriedTensor _) (.up ℤ) p q n hpq ▷ P.X r)
      ≫ HomologicalComplex.ιMapBifunctor (pullbackTensorTotal Y F V) P
        (curriedTensor _) (.up ℤ) n r k hnr ≫
          (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F
            (f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F))).f k =
    (if h : r + q = 0 then
      (α_ (F.X p) (V.X q) (P.X r)).hom ≫
        F.X p ◁ ((β_ (V.X q) (P.X r)).hom ≫
          (SheafOfModules.tensorHomEquiv (R := Y.sheaf) (P.X r) (V.X q)
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).symm
              (π P O q r 0 h ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (P.X r))
                (HomologicalComplex.singleObjXSelf (.up ℤ) 0
                  (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).hom)) ≫
        (ρ_ (F.X p)).hom ≫ (F.XIsoOfEq (by omega : p = k)).hom
    else 0) ≫ (eta.app F).f k := by
  classical
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex (R := Y.sheaf) P O
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  have h₁ := schemeTensorHomUncurry_summand_naturality Y P F V f p q r n k hpq hnr
  have h₂ := schemeOrdinaryEvaluation_uncurried_component Y P F f hf p q r n k hpq hnr
  exact h₁.trans (congrArg (fun t ↦ t ≫ (eta.app F).f k) h₂)

end AlgebraicGeometry
