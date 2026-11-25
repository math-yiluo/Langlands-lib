/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralShapes
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralGlue
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralShapes
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralGlue
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceVaryingScalarSquare
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryEndpointMaps
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalEvaluationUnit
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import all WeilConjectures.AlgebraicGeometry.ScalarUnitExtComparison
import all WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

/-! # Integral normalization of a finite étale lift -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  comparisonUpperStar diagonalFiniteToPadic diagonalForget SpTowerClasses.lineModule

open SpTowerClasses
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open WeilConjectures
attribute [local implicit_reducible] spCoefficientCommRings
  SpTowerShriek.tau Functor.ofOpSequence Functor.ofSequence
  SemilinearSections.evaluation
attribute [local irreducible] SemilinearSections.scalarExtensionSection
  cartierProRootMap

attribute [local semireducible] diagonalForget SpTowerClasses.lineModule

section IntegralBoundaryCalculation

attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [local implicit_reducible] CategoryTheory.constantSheaf comparisonLowerStar
  Functor.sheafPushforwardContinuous Scheme.toProEt

attribute [local irreducible] Ext.comp Ext.mk₀ Ext.mk₀CompMk₀
  Ext.mapExactFunctor Ext.homEquiv diagonalForget SpTowerClasses.lineModule
attribute [local implicit_reducible] geoCartierLine
attribute [local instance 100000] integralAbDerived

/-- The integral adjunct of a supplied lift is the evaluated tower Kummer composite.
The right side uses only the tower extension and the pro-etale root map; it makes
no assertion identifying that composite with an etale cohomology class.

Source: geometric tower classes proof (2), finite scalar-unit square and evaluation;
diagonal trace proof (2), coefficient-one and root-tensor coordinates.
(blueprint: lem-sfb-diagonal-trace-finite-etale-integral-boundary).

Proof: apply hc to P,n and remove its HEq witnesses. Forget hb to abelian sheaves
using forgottenFiniteEquation. The natural isomorphism evalIso identifies the
underlying restricted functor with intrinsic finite evaluation. Transport the
coefficient source through this isomorphism and the frame. On constant one,
finiteQuotient, restrictionInverseSection and a.coefficient_one show that it
is the site-comparison integral generator. The constant-sheaf adjunction and
additivity extend this equality to all sections. At the target use rootEndpoint,
whose proved section calculation uses the scalar unit and k.line_tensor.
Naturality of exact single-arrow transport now pastes the two endpoint squares
with the finite boundary equality. Ext.homEquiv is injective, so the resulting
hom identity is the stated Ext identity. Ext.mapExactFunctor and the natural
forgetComparisonIso move ordinary coefficient forgetting past site comparison.
This argument does not compare the tower Kummer extension with the etale one,
and never cancels arbitrary derived scalar restriction. -/
theorem diagonalTrace_finiteEtale_integralBoundary
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (P : (diagonalSurface Y).Pic)
    (b : Ext (Etale.ordinaryFiniteConstant (diagonalResidue.{u} l n)
      (diagonalSurface Y)) (Scheme.finiteEtaleTateLine (diagonalSurface Y)
        (l ^ (n + 1)) (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))) 2)
    (hb : finiteEvaluationEquation r.F (diagonalFiniteToPadic l n (diagonalSurface Y)) n
      a.coefficient a.line (SpTowerClasses.firstChern l (ULift.{u} (Padic l)) c P)
      (finiteEtaleProImage (diagonalResidue.{u} l n) (diagonalSurface Y)
        (l ^ (n + 1)) (cartierResidue_cast l (n + 1)) b)) :
    Ext.mk₀CompMk₀ (integerComparison (diagonalSurface Y)).inv
      ((Etale.ordinaryFiniteClass (diagonalResidue l n) (diagonalSurface Y)
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) (l ^ (n + 1))
          (diagonalResidue l n) (cartierResidue_cast l (n + 1))) 2
        (Etale.ordinaryFiniteExtHomEquiv (diagonalResidue l n) (diagonalSurface Y)
          _ _ 2 b)).mapExactFunctor
            (comparisonUpperStar AddCommGrpCat.{u + 1} (diagonalSurface Y)))
      ((forgetComparisonIso (diagonalResidue l n) (diagonalSurface Y)).hom.app
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) (l ^ (n + 1))
          (diagonalResidue l n) (cartierResidue_cast l (n + 1)))) =
    evaluatedIntegralKummerClass l (diagonalSurface Y) (diagonalResidue l n) n
      (cartierResidue_cast l (n + 1)) c.kummer
      (diagonalSurface_power_unit l Y hY n) P := by
  rw [← integralImage]
  apply Ext.ext.{u + 1}
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext,
    evaluatedIntegralKummerClass_hom]
  exact integralBoundaryGlue l Y hY c r n P _ _ a.coefficient a.line hb
    (chernBoundary l Y c hc n P) (sourceEndpoint l Y hY c r k n a)
    (rootEndpoint l Y hY c r k n a)

end IntegralBoundaryCalculation

end AlgebraicGeometry.ProEtale.DiagonalTrace
