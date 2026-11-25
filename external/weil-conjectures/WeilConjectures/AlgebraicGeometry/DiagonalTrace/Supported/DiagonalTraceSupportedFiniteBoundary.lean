/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceConeNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundaryEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundarySource
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryTarget
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryCombine

/-! # The finite Chern equation for a normalized strict supported Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap

/-- Project a normalized strict supported Cartier class, then forget its support.
The result is the finite Chern arrow. The input is a strict degree-two Ext class
and an ordinary source cone; there is no completed diagonal arrow or limit-arrow
characterization in this assertion.

Source: diagonal trace proof (2), finite Cartier normalization and forgetting
support; diagonal-system proof (4), positive finite reductions; geometric classes
proof (2)--(3), finite Chern normalization.
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary).

Proof: project the ordinary source cone at n. Its generator equation followed by
DiagonalSourceNormalization identifies this map on the integral supported
constant with the canonical quotient generator at exponent n+1. The explicit
completedSupportedUnit carries one to the supported section one. Apply the
finite-cycle equation to the evaluation of xi, transporting its endpoints by
the source and root isomorphisms in that equation. The normalization of e fixes
the target transport on every root. Cartier reduction uniqueness and site
comparison identify this class with the positive supported Kummer class.
The supported Kummer Chern realization then identifies its integral adjunct
after forgetting support with the Kummer Chern class of the dual diagonal ideal,
namely diagonalPic Y. Apply hc to this Picard class and n. The coefficient-one
and root-tensor equations of k identify its quotient and root maps with these
same finite maps; hn fixes the positive Kummer boundary and scalar comparisons.
The completed coefficient ring is l-regular with actual quotient the finite
constant ring at exponent n+1. Derived reduction of its unit is therefore the
finite unit, with adjunct the actual coefficient projection. First use this
reduction adjunction and then the integral-to-finite scalar-unit Ext bijection
to conclude equality of coefficient-linear arrows from their integral adjuncts.
Finally the exact-cone projection identity replaces the source coefficient
projection by k.unitMap followed by L.projection. These arguments include n=0,
since its exponent is one, and the empty scheme, where all maps are unique. -/
theorem diagonalTrace_supportedFiniteBoundary
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : Ext (D.E.obj (diagonalIntegralSource Y)) H 2)
    (hxi : FiniteCartierNormalization l Y hY D H roots xi)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (hs : SupportedSourceConeNormalization l Y D s)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (he : Functor.whiskerRight e.hom (diagonalForget l (diagonalSurface Y)) =
      roots.hom ≫ k.lineForget.inv)
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (hp : p.Presents xi)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) :
    finiteBoundaryEquation l Y D H p s c r k e L₀ L n  := by
  obtain ⟨a, ha⟩ := diagonalTrace_supportedFiniteBoundary_sourceStep
    l Y hY D H roots xi hxi s hs c r k e he p hp L₀ L n
  exact diagonalTrace_supportedFiniteBoundary_combine
    l Y hY D H s c r k e p L₀ L n a ha
    (diagonalTrace_supportedFiniteBoundary_targetStep l Y hY c hn hc r k n a L _
      (diagonalTrace_supportedFiniteBoundary_cartierKummer l Y hY n))

end AlgebraicGeometry.ProEtale.DiagonalTrace
