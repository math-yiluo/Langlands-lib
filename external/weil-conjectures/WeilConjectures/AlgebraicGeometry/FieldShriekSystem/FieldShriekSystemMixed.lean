/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemTransitionWords
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-system comparison laws

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-mixed).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard
attribute [local irreducible] restrictionEvaluation supportEvaluation comparison

/-- The transition square of the actual system comparison, in both scalar paths.
The reductions are transposes of SemilinearSections.derivedTransition. Evaluation
coordinates are the ones in the inherited EvaluationLaw, and the common right side
contains compact support of the input transition, not just a finite coefficient cocycle.
Source: blueprint (2), mixed quotient compatibility, proof step 8
(blueprint: def-sp-field-shriek-system-mixed). -/
structure MixedLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    extends EvaluationLaw P D c where
  quotientCoordinates : ∀ (E : Index P) (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n),
    QuotientRestriction P E T v
  coefficientSquare : ∀ (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n),
    (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v)
  system_square : ∀ (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n)
    (M : SpTowerShriek.D P.coefficients.l E.val X), normalized P D E X M →
    ComparisonTransitionSquare P D c h v (quotientCoordinates F Y v) M
  mixed : ∀ (E F : Index P) (h : E ≤ F) (m n : ℕ) (v : m ≤ n)
    (M : SpTowerShriek.D P.coefficients.l E.val X), normalized P D E X M →
    HEq (quotientAfterComparison P D c toEvaluationLaw h v (quotientCoordinates F Y v) M)
      (commonTransitionComparison P D c h v (coefficientSquare E F h m n v)
        (quotientCoordinates E X v) M) ∧
    HEq (comparisonAfterQuotient P D c toEvaluationLaw h v (quotientCoordinates E Y v) M)
      (commonTransitionComparison P D c h v (coefficientSquare E F h m n v)
        (quotientCoordinates E X v) M)

end AlgebraicGeometry.ProEtale.FieldShriekSystem
