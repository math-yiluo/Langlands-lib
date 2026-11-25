/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
public import WeilConjectures.AlgebraicGeometry.SchemeTensorUnitAction
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationChainMapExists
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationChainAction

/-! # Ordinary evaluation before localization
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ.
(blueprint: lem-pc-scheme-ordinary-evaluation-chain-calculation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- Elaborating total tensor associators uses the sheaf tensor and coproduct instances.
/-- Ordinary evaluation is tensoring the chain evaluation into the single unit.
Source: Stacks Project, cohomology.tex, Tags 08DJ, 08DM and 08DQ;
ordinary evaluation localization proof step 2.
(blueprint: lem-pc-scheme-ordinary-evaluation-chain-calculation).

Proof: Construct e degreewise by extending evaluation of Hom(P,O)^q on P^r
across the coproduct defining Tot(V,P). Its target is O^(q+r). The Hom
projection differential formula and the tensor differential give the chain-map
law, including the Koszul sign. Naturality of the tensor-Hom adjunction in the
coefficient augmentation gives the first equation. For the second equation,
restrict to F^p tensor V^q tensor P^r. Apply the ordinary evaluation component
formula hf and cancel currying with uncurrying. If q+r is nonzero, the single
unit component vanishes and both composites are zero. If q+r is zero, its
singleObjXSelf identification turns the component into the right unit action
on F^p. The tensor associator has no sign and reindexes exactly these summands.
Coproduct extensionality twice gives the second chain-map equality. No derived
category or invertibility of a tensor comparison enters this argument; it works
for unbounded complexes, zero complexes and the empty scheme. -/
theorem schemeOrdinaryEvaluation_chain_calculation (Y : Scheme.{u})
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let phiF := f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F)
    let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
    ∃ e : pullbackTensorTotal Y V P ⟶ O,
      schemeTensorHomUncurry Y V P O phiO = e ≫ eta.app O ∧
      schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F phiF =
        schemeTensorUnitAction Y F V P e ≫ eta.app F := by
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  obtain ⟨e, hO⟩ := schemeOrdinaryEvaluation_chain_map_exists Y P
  have hF := schemeOrdinaryEvaluation_chain_action Y P F f hf e hO
  exact ⟨e, hO, hF⟩

end AlgebraicGeometry
