/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedSliceTensorGenerators
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coherent compact-support comparison on coefficient systems

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension,
sk-lem-sp-field-extension-towers.proof.md (2), proper/open system comparison
(blueprint: def-sp-field-shriek-system-models).

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
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

variable (P : PurityFiniteSetting.{u})

/-- Finite fields in the fixed coefficient closure, with their actual inclusions.
Source: blueprint (2), E subset F (blueprint: def-sp-field-shriek-system-models). -/
abbrev Index := Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar

/-- Canonical quotient and whole-ring-system maps, fixed on every residue class.
Source: blueprint (2), coefficient square
(blueprint: def-sp-field-shriek-system-models). -/
structure Coefficients (E F : Index P) (h : E ≤ F) where
  quotient : ∀ n : ℕ,
    SpTowerShriek.R P.coefficients.l E.val n →+* SpTowerShriek.R P.coefficients.l F.val n
  quotient_mk : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers P.coefficients.l E.val),
    quotient n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _
      (integralScalarIntegerInclusion P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) x)
  tower : ∀ T : Scheme.{u},
    spCoefficientCommRings P.coefficients.l E.val T ⟶
      spCoefficientCommRings P.coefficients.l F.val T
  tower_app : ∀ (T : Scheme.{u}) (n : ℕ), (tower T).app (op n) =
    (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((quotient n).comp (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))

/-- The actual coefficient morphism on the entire sequence site.
Source: blueprint (2), simultaneous models
(blueprint: def-sp-field-shriek-system-models). -/
def coefficientMap {E F : Index P} {h : E ≤ F} (a : Coefficients P E F h)
    (T : Scheme.{u}) :=
  SemilinearSections.systemMap (Scheme.ProEt.topology T)
    (SpTowerShriek.B P.coefficients.l E.val T) (SpTowerShriek.tau P.coefficients.l E.val T)
    (SpTowerShriek.B P.coefficients.l F.val T) (SpTowerShriek.tau P.coefficients.l F.val T)
    (fun n ↦ (a.tower T).app (op n))
    (fun n ↦ ((a.tower T).naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- Scalar extension is the dependency's universal K-flat normalized scalar extension.
Source: blueprint (2), C_T (blueprint: def-sp-field-shriek-system-models). -/
abbrev Scalars {E F : Index P} {h : E ≤ F} (a : Coefficients P E F h) (T : Scheme.{u}) :=
  SemilinearSections.ScalarData (coefficientMap P a T)

/-- Normalize the geometric/scalar pullback square before localization. The pushforward
restriction square is literally the identity on sections, and the pullback square is
its double adjunction mate. The derived square has its cochain normalization, so a
transformation invisible to evaluations cannot be added.
Source: blueprint (2), lambda_a on simultaneous models
(blueprint: def-sp-field-shriek-system-models). -/
structure PullComparison {E F : Index P} {h : E ≤ F}
    (a : Coefficients P E F h) (bE : SpTowerShriek.Base P.coefficients.l E.val)
    (bF : SpTowerShriek.Base P.coefficients.l F.val)
    (oE : SpTowerShriek.Operations P.coefficients.l E.val bE)
    (oF : SpTowerShriek.Operations P.coefficients.l F.val bF)
    (s : ∀ T : Scheme.{u}, Scalars P a T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  restrictionPush : SemilinearSections.res (coefficientMap P a X) ⋙ (oE.geometry f).push ≅
    (oF.geometry f).push ⋙ SemilinearSections.res (coefficientMap P a Y)
  sections : ∀ (M : SpTowerShriek.S P.coefficients.l F.val X)
    (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : ((SemilinearSections.res (coefficientMap P a X) ⋙
      (oE.geometry f).push).obj M).val.obj U),
    HEq (((restrictionPush.hom.app M).val.app U) x) x
  ordinary : (s Y).model.E ⋙ (oF.geometry f).pull ≅
    (oE.geometry f).pull ⋙ (s X).model.E
  ordinary_mate :
    (mateEquiv (s Y).ordinaryAdjunction (s X).ordinaryAdjunction ordinary.inv) =
      ((mateEquiv (oF.geometry f).ordinaryAdjunction
        (oE.geometry f).ordinaryAdjunction).symm restrictionPush.inv)
  derived : (s Y).T ⋙ SpTowerShriek.pull P.coefficients.l F.val bF (oF.geometry f) ≅
    SpTowerShriek.pull P.coefficients.l E.val bE (oE.geometry f) ⋙ (s X).T
  representative : ∀ (K : CochainComplex (SpTowerShriek.S P.coefficients.l E.val Y) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing (Scheme.ProEt.topology Y)
        (SpTowerShriek.B P.coefficients.l E.val Y)
        (SpTowerShriek.tau P.coefficients.l E.val Y)) K →
    derived.hom.app (DerivedCategory.Q.obj K) ≫
        (s X).T.map ((oE.geometry f).pull.mapDerivedCategoryFactors.hom.app K) ≫
        (s X).model.ε.app (((oE.geometry f).pull.mapHomologicalComplex (.up ℤ)).obj K) =
      (SpTowerShriek.pull P.coefficients.l F.val bF (oF.geometry f)).map
          ((s Y).model.ε.app K) ≫
        (oF.geometry f).pull.mapDerivedCategoryFactors.hom.app
          (((s Y).model.E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app K)

/-- All coefficient and operation presentations needed to construct b. Every datum is
normalized by the recorded universal constructions, not an arbitrary natural map.
Source: blueprint (2), proper/open construction
(blueprint: def-sp-field-shriek-system-models). -/
structure Models where
  base : ∀ E : Index P, SpTowerShriek.Base P.coefficients.l E.val
  operations : ∀ E : Index P, SpTowerShriek.Operations P.coefficients.l E.val (base E)
  coordinates : ∀ E : Index P, SpTowerCalculus.Coordinates P.coefficients.l E.val (base E)
  coefficients : ∀ (E F : Index P) (h : E ≤ F), Coefficients P E F h
  scalars : ∀ (E F : Index P) (h : E ≤ F) (T : Scheme.{u}),
    Scalars P (coefficients E F h) T
  pull : ∀ (E F : Index P) (h : E ≤ F) {X Y : Scheme.{u}} (f : X ⟶ Y),
    PullComparison P (coefficients E F h) (base E) (base F)
      (operations E) (operations F) (scalars E F h) f
  openIso : ∀ (E F : Index P) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    SpTowerShriek.openD P.coefficients.l E.val (base E) ((operations E).openOp j) ⋙
        (scalars E F h Z).T ≅
      (scalars E F h X).T ⋙
        SpTowerShriek.openD P.coefficients.l F.val (base F) ((operations F).openOp j)
  open_unit : ∀ (E F : Index P) (h : E ≤ F) {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j],
    (openIso E F h j).inv =
      ((mateEquiv ((operations E).openOp j).derivedAdjunction
        ((operations F).openOp j).derivedAdjunction).symm (pull E F h j).derived.inv)

/-- The proper coefficient comparison is the actual geometric counit mate.
Source: blueprint (2), a_h (blueprint: def-sp-field-shriek-system-models). -/
def proper (D : Models P) {E F : Index P} (h : E ≤ F)
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :=
  (mateEquiv
    (SpTowerShriek.adjunction P.coefficients.l E.val (D.base E) ((D.operations E).geometry g))
    (SpTowerShriek.adjunction P.coefficients.l F.val (D.base F) ((D.operations F).geometry g))
    (D.pull E F h g).derived.hom)

/-- The specified whole-system b: proper counit mate, followed by proper image of
open tensor identification. The same compactification occurs on both sides.
Source: blueprint (2), b_a = Q_B(e_a) a_h J_A
(blueprint: def-sp-field-shriek-system-models). -/
def comparison (D : Models P) {E F : Index P} (h : E ≤ F)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    SpTowerShriek.F P.coefficients.l E.val (D.base E) (D.operations E) c ⋙
        (D.scalars E F h Y).T ⟶
      (D.scalars E F h X).T ⋙
        SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F) c :=
  Functor.whiskerLeft
      (SpTowerShriek.openD P.coefficients.l E.val (D.base E) ((D.operations E).openOp c.i))
      (proper P D h c.g) ≫
    Functor.whiskerRight (D.openIso E F h c.i).hom
      (SpTowerShriek.push P.coefficients.l F.val (D.base F) ((D.operations F).geometry c.g))

/-- The recorded normalized constructible predicate, in the section-preserving
sequence-site coordinates. Uniform cohomological and Tor bounds are retained.
Source: blueprint (2), N_A (blueprint: def-sp-field-shriek-system-models). -/
def normalized (D : Models P) (E : Index P) (T : Scheme.{u}) :
    ObjectProperty (SpTowerShriek.D P.coefficients.l E.val T) :=
  fun K ↦ spNormalizedConstructibleTorTowers P.coefficients.l E.val T
    ((D.coordinates E).abelian T)
    ((SpTowerCalculus.realization P.coefficients.l E.val (D.base E) T
      ((D.coordinates E).abelian T)).inverse.obj K)


end AlgebraicGeometry.ProEtale.FieldShriekSystem
