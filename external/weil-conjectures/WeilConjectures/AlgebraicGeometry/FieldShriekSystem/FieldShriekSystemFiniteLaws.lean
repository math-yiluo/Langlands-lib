/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-system comparison laws

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-finite-laws).

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

/-- Finite evaluation with its actual scalar and support coordinates.
Source: blueprint (2), specified finite b
(blueprint: def-sp-field-shriek-system-finite-laws). -/
structure EvaluationLaw (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  scalarEvaluation : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}) (n : ℕ),
    ScalarEvaluation P D h T n
  supportCoordinates : ∀ (E : Index P) (n : ℕ), FiniteCoordinates P E c n
  evaluation : ∀ (E F : Index P) (h : E ≤ F) (n : ℕ)
    (M : SpTowerShriek.D P.coefficients.l E.val X),
    (SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M) ≫
        (supportEvaluation P D F c n (supportCoordinates F n)).hom.app
          ((D.scalars E F h X).T.obj M) ≫
        (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).map
          ((scalarEvaluation E F h X n).iso.hom.app M) =
      (scalarEvaluation E F h Y n).iso.hom.app
          ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).map
          ((supportEvaluation P D E c n (supportCoordinates E n)).hom.app M) ≫
        (reductionDirectImageComparison ((D.coefficients E F h).quotient n) c.i c.g).app
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)



end AlgebraicGeometry.ProEtale.FieldShriekSystem
