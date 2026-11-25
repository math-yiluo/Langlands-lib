/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemTransitions
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-system comparison laws

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-transition-words).

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

/-- First path of the actual b transition square: apply b at n, then the target
system's reduction. Scalar associativity identifies its source with the composite map.
Source: blueprint (2), proof step 8, R_n to S_n to S_m
(blueprint: def-sp-field-shriek-system-transition-words). -/
@[irreducible] def quotientAfterComparison (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : EvaluationLaw P D c) {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (q : QuotientRestriction P F Y v) (M : SpTowerShriek.D P.coefficients.l E.val X) :=
  (scalarExtensionFunctor_composition ((D.coefficients E F h).quotient n)
      (SpTowerCalculus.quotient P.coefficients.l F.val v) Y).inv.app
        ((reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) ≫
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) Y).map
      ((comparisonSource P D c e h n M).inv ≫
        (SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M)) ≫
    systemReduction P F Y v q
      ((SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).obj
        ((D.scalars E F h X).T.obj M)) ≫
    (comparisonTarget P D c e h m M).hom

/-- Second path of the actual b transition square: reduce the source support system,
then apply b at m. It uses that system's own transition, not a finite cocycle substitute.
Source: blueprint (2), proof step 8, R_n to R_m to S_m
(blueprint: def-sp-field-shriek-system-transition-words). -/
@[irreducible] def comparisonAfterQuotient (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (e : EvaluationLaw P D c) {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (q : QuotientRestriction P E Y v) (M : SpTowerShriek.D P.coefficients.l E.val X) :=
  (scalarExtensionFunctor_composition (SpTowerCalculus.quotient P.coefficients.l E.val v)
      ((D.coefficients E F h).quotient m) Y).inv.app
        ((reductionCompactSupport (SpTowerShriek.R P.coefficients.l E.val n) c.i c.g).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) ≫
    (scalarExtensionFunctor ((D.coefficients E F h).quotient m) Y).map
      ((scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) Y).map
          ((supportEvaluation P D E c n (e.supportCoordinates E n)).inv.app M) ≫
        systemReduction P E Y v q
          ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M)) ≫
    (e.scalarEvaluation E F h Y m).iso.inv.app
      ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≫
    (SpTowerShriek.Ev P.coefficients.l F.val Y m).map ((comparison P D h c).app M) ≫
    (comparisonTarget P D c e h m M).hom

/-- The square for b as a morphism between its source and target whole systems.
Both vertical maps come from their own derived strict transitions via scalar adjunction.
Source: blueprint (2), proof step 8, transition square of b_a
(blueprint: def-sp-field-shriek-system-transition-words). -/
@[irreducible] def ComparisonTransitionSquare (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (q : QuotientRestriction P F Y v) (M : SpTowerShriek.D P.coefficients.l E.val X) : Prop :=
  (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l F.val v) Y).map
      ((SpTowerShriek.Ev P.coefficients.l F.val Y n).map ((comparison P D h c).app M)) ≫
    systemReduction P F Y v q
      ((SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c).obj
        ((D.scalars E F h X).T.obj M)) =
  systemReduction P F Y v q
      ((D.scalars E F h Y).T.obj
        ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M)) ≫
    (SpTowerShriek.Ev P.coefficients.l F.val Y m).map ((comparison P D h c).app M)

/-- The common right side of the transition square: the specified finite b for
R_n to S_m, followed by compact support of the actual input system transition.
The coefficient-square equality transports only the source scalar action.
Source: blueprint (2), proof step 8, common composite comparison
(blueprint: def-sp-field-shriek-system-transition-words). -/
@[irreducible] def commonTransitionComparison (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {E F : Index P} (h : E ≤ F) {m n : ℕ} (v : m ≤ n)
    (hc : (SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n) =
      ((D.coefficients E F h).quotient m).comp
        (SpTowerCalculus.quotient P.coefficients.l E.val v))
    (q : QuotientRestriction P E X v) (M : SpTowerShriek.D P.coefficients.l E.val X) :=
  (reductionDirectImageComparison
      ((SpTowerCalculus.quotient P.coefficients.l F.val v).comp
        ((D.coefficients E F h).quotient n)) c.i c.g).app
      ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) ≫
    (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val m) c.i c.g).map
      (eqToHom (congrArg (fun a ↦ (scalarExtensionFunctor a X).obj
          ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M)) hc) ≫
        (scalarExtensionFunctor_composition
          (SpTowerCalculus.quotient P.coefficients.l E.val v)
          ((D.coefficients E F h).quotient m) X).inv.app
            ((SpTowerShriek.Ev P.coefficients.l E.val X n).obj M) ≫
        (scalarExtensionFunctor ((D.coefficients E F h).quotient m) X).map
          (systemReduction P E X v q M))

end AlgebraicGeometry.ProEtale.FieldShriekSystem
