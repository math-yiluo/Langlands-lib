/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Exceptional.ExceptionalSystemOrdinaryPullbackSquare
import WeilConjectures.CategoryTheory.SixFunctors.IndependentLocalizedCube
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Normalized system pullback squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry

attribute [local instance 20000] strictEtaleSystemDerived strictEtaleLevelDerived
  exceptionalProSystemDerived exceptionalProLevelDerived

variable {O : Type (u + 1)} [CommRing O] {ell : O}

/-- The canonical geometric pullback square on systems and its finite levels.
Source: Zheng Construction 4.1; Stacks 099R and 0B65.
(blueprint: lem-sf-exceptional-system-pullback-square-construction).

Proof: Obtain the canonical ordinary system and finite-level pullback comparisons
with their underlying and evaluation equations. Full faithfulness of precomposition
with the localization of complexes produces a derived comparison from each ordinary
comparison, with its representative formula. Apply the localization cube lemma to
these two comparison faces and the four prescribed inverse-evaluation faces. Their
six representative equations identify the resulting derived cube with the ordinary
evaluation cube. This gives derived evaluation coherence. The constructed data and
the four remaining equations form the normalized pullback-square record. -/
theorem exceptionalSystemPullbackSquare_exists
    [∀ n : ℕ, Finite (O ⧸ (Ideal.span ({ell} : Set O)) ^ (n + 1))]
    {T U : Scheme.{u}} (g : T ⟶ U)
    {PT : StrictEtaleEvaluation T O ell} {PU : StrictEtaleEvaluation U O ell}
    (CT : ExceptionalSystemSiteComparison O ell T PT)
    (CU : ExceptionalSystemSiteComparison O ell U PU)
    (E : StrictEtaleOrdinaryImage O ell g) (P : ExceptionalProOrdinaryImage O ell g)
    (ED : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := U.smallEtaleTopology) (K := T.smallEtaleTopology) O ell _ _ _ E PU PT)
    (PD : CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology U) (K := Scheme.ProEt.topology T) O ell _ _ _ P
      CU.proEvaluation CT.proEvaluation) :
    Nonempty (ExceptionalSystemPullbackSquare g CT CU E P ED PD) := by
  obtain ⟨ρ, ρn, hu, hev⟩ := exceptionalSystemOrdinaryPullbackSquare_exists g CT CU E P
  obtain ⟨δ, hδ⟩ := derivedSquare_exists CU.ordinary.inverse E.inverse P.inverse
    CT.ordinary.inverse CU.image.system.inverse ED.system.inverse PD.system.inverse
    CT.image.system.inverse CU.image.system.inverseFactors ED.system.inverseFactors
    PD.system.inverseFactors CT.image.system.inverseFactors ρ
  have hl (n : ℕ) := derivedSquare_exists (CU.ordinary.lift n).modules (E.lift n).modules
    (P.lift n).modules (CT.ordinary.lift n).modules (CU.image.level n).inverse
    (ED.level n).inverse (PD.level n).inverse (CT.image.level n).inverse
    (CU.image.level n).inverseFactors (ED.level n).inverseFactors
    (PD.level n).inverseFactors (CT.image.level n).inverseFactors (ρn n)
  choose δn hδn using hl
  let record : ExceptionalSystemPullbackSquareData g CT CU E P ED PD :=
    { ordinary := ρ
      level := ρn
      square := δ
      derivedLevel := δn }
  refine ⟨⟨record, hu, hev, hδn, ?_, hδ⟩⟩
  intro n M
  have hc := localized_exactCube
    CU.ordinary.inverse P.inverse
    (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology T) n)
    E.inverse CT.ordinary.inverse (coefficientEvaluation.{u + 1, u, u + 1} (J :=
      T.smallEtaleTopology) n)
    (CT.ordinary.lift n).modules (coefficientEvaluation.{u + 1, u, u + 1} (J :=
      U.smallEtaleTopology) n)
    (E.lift n).modules (coefficientEvaluation.{u + 1, u, u + 1} (J := Scheme.ProEt.topology U) n)
    (P.lift n).modules (CU.ordinary.lift n).modules
    CU.image.system.inverse PD.system.inverse (CT.proEvaluation.evaluation n)
    ED.system.inverse CT.image.system.inverse (PT.evaluation n)
    (CT.image.level n).inverse (PU.evaluation n) (ED.level n).inverse
    (CU.proEvaluation.evaluation n) (PD.level n).inverse (CU.image.level n).inverse
    CU.image.system.inverseFactors PD.system.inverseFactors
    (CT.proEvaluation.evaluationFactors n) ED.system.inverseFactors
    CT.image.system.inverseFactors (PT.evaluationFactors n) (CT.image.level n).inverseFactors
    (PU.evaluationFactors n) (ED.level n).inverseFactors (CU.proEvaluation.evaluationFactors n)
    (PD.level n).inverseFactors (CU.image.level n).inverseFactors
    ρ (CT.ordinary.inverseEvaluation n) (E.inverseEvaluation n)
    (P.inverseEvaluation n) (CU.ordinary.inverseEvaluation n) (ρn n)
    δ (CT.image.inverseEvaluation n) (ED.inverseEvaluation n)
    (PD.inverseEvaluation n) (CU.image.inverseEvaluation n) (δn n)
    hδ (CT.image.inverseEvaluation_rep n) (ED.inverseEvaluation_rep n)
    (PD.inverseEvaluation_rep n) (CU.image.inverseEvaluation_rep n) (hδn n) (hev n)
  exact congr_app hc M

end AlgebraicGeometry
