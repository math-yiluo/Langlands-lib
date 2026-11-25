/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemFiniteLaws
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSupportEvaluation
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-system comparison laws

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-transitions).

All arrows below live in the ordinary derived category of the ringed sequence site.
The recorded section-preserving equivalence identifies this with the original strict
tower category. Index n denotes positive exponent n+1. The structures package the
specified constructions and their laws as conclusions, rather than assuming the
comparison or choosing a lift of its finite evaluations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

attribute [local irreducible] coefficientMap HasDerivedCategory.standard
attribute [local irreducible] restrictionEvaluation supportEvaluation comparison

/-- Quotient restriction in the actual ell-power sequence model. Its comparison
with constant-ring restriction is fixed to identity on every section.
Source: blueprint (2), input transitions (proof step 8)
(blueprint: def-sp-field-shriek-system-transitions). -/
structure QuotientRestriction (E : Index P) (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n) where
  ordinary : SemilinearSections.res
      (SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T) v) ≅
    proEtaleRingRestrictScalars
      (proEtaleConstantRingMap (T := T) (SpTowerCalculus.quotient P.coefficients.l E.val v))
  sections : ∀ (N : proEtaleRingModules T
      (proEtaleConstantRing T (SpTowerShriek.R P.coefficients.l E.val m)))
    (U : T.ProEtᵒᵖ) (x : ((SemilinearSections.res
      (SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
        (SpTowerShriek.B P.coefficients.l E.val T)
        (SpTowerShriek.tau P.coefficients.l E.val T) v)).obj N).val.obj U),
    HEq (((ordinary.hom.app N).val.app U) x) x

/-- Reduction is the actual derived strict transition transposed under finite scalar
adjunction, after exact localization of the section-identity restriction comparison.
Source: blueprint (2), proof step 8; Zheng 4.1
(blueprint: def-sp-field-shriek-system-transitions). -/
@[irreducible] def systemReduction (E : Index P) (T : Scheme.{u}) {m n : ℕ} (v : m ≤ n)
    (q : QuotientRestriction P E T v) (N : SpTowerShriek.D P.coefficients.l E.val T) :
    (scalarExtensionFunctor (SpTowerCalculus.quotient P.coefficients.l E.val v) T).obj
      ((SpTowerShriek.Ev P.coefficients.l E.val T n).obj N) ⟶
        (SpTowerShriek.Ev P.coefficients.l E.val T m).obj N :=
  by
    letI := proEtaleRingRestrictScalars_preservesFiniteLimits
      (proEtaleConstantRingMap (T := T) (SpTowerCalculus.quotient P.coefficients.l E.val v))
    letI := proEtaleRingRestrictScalars_preservesFiniteColimits
      (proEtaleConstantRingMap (T := T) (SpTowerCalculus.quotient P.coefficients.l E.val v))
    exact
      (finiteScalarAdjunction (SpTowerCalculus.quotient P.coefficients.l E.val v) T).homEquiv _ _
        |>.symm ((SemilinearSections.derivedTransition (Scheme.ProEt.topology T)
            (SpTowerShriek.B P.coefficients.l E.val T)
            (SpTowerShriek.tau P.coefficients.l E.val T) v).app N ≫
          (Functor.mapDerivedCategoryNatIso q.ordinary).hom.app
            ((SpTowerShriek.Ev P.coefficients.l E.val T m).obj N))

/-- Source evaluation coordinates of b use the specified scalar and support maps.
Source: blueprint (2), evaluation of the source (proof steps 3 and 8)
(blueprint: def-sp-field-shriek-system-transitions). -/
@[irreducible] def comparisonSource (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : EvaluationLaw P D c) {E F : Index P} (h : E ≤ F)
    (n : ℕ) (M : SpTowerShriek.D P.coefficients.l E.val X) :=
  (e.scalarEvaluation E F h Y n).iso.app
      ((SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c).obj M) ≪≫
    (scalarExtensionFunctor ((D.coefficients E F h).quotient n) Y).mapIso
      ((supportEvaluation P D E c n (e.supportCoordinates E n)).app M)

/-- Target evaluation coordinates of b retain the actual scalar/open/proper word.
Source: blueprint (2), evaluation of the target (proof steps 3 and 8)
(blueprint: def-sp-field-shriek-system-transitions). -/
@[irreducible] def comparisonTarget (D : Models P) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : EvaluationLaw P D c) {E F : Index P} (h : E ≤ F)
    (n : ℕ) (M : SpTowerShriek.D P.coefficients.l E.val X) :=
  (supportEvaluation P D F c n (e.supportCoordinates F n)).app
      ((D.scalars E F h X).T.obj M) ≪≫
    (reductionCompactSupport (SpTowerShriek.R P.coefficients.l F.val n) c.i c.g).mapIso
      ((e.scalarEvaluation E F h X n).iso.app M)

end AlgebraicGeometry.ProEtale.FieldShriekSystem
