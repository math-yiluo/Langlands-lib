/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceConeNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryEquation
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteFrameConstruction
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedOrdinaryFiniteUnit
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryCoordinates
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteCoordinateAssembly
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalizedCoordinates

/-! # The finite Chern equation for a normalized strict supported Cartier class -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap diagonalCompletedRestriction

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
  completedSupportedUnit

/-- The projected supported strict class is the canonical finite Cartier arrow.
This assertion has no Chern normalization hypothesis: its endpoint is the reduced
Cartier class, not the Chern composite. The coordinates are normalized on one and
on roots, so the displayed endpoint cannot be chosen to fit the source composite.

Source: diagonal trace proof (2), source projection; diagonal-system proof (4).
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-source-step).

Proof: compose k.coefficientForget with the canonical constant finite-ring
comparison to identify the evaluated coefficient unit with the constant residue
module. The residue-action equation of r makes this comparison linear, and
k.coefficient_one fixes its value on one. At level n take the source and root
isomorphisms sigma,t from hxi. Define the frame line isomorphism by e_n inverse
followed by t. FiniteRootNormalization and he give exactly a.line_roots.
Compose hs at n with the forgotten source coordinate sigma. The source
normalization in hxi identifies the resulting integral generator with the canonical
positive finite quotient. Apply the ordinary finite-unit equation to this source
map: completedSupportedUnit followed by the source map is the finite
constant-to-supported unit after the actual coefficient projection and the
coefficient coordinate. This ordinary equation is the remaining sheaf calculation.
Use hp to replace the presented arrow by xi, and the n-th finite-cycle equation
in hxi to replace its normalized evaluation by cartierResidueReducedPro.
The root normalization in hxi and he identify the target comparison with the
frame line coordinates. Finally the exact-cone projection equation identifies
the coefficient input for any L with its actual n-th projection. This proves the
stated supportedBoundaryEquation for arbitrary L₀ and L. The exponent is n+1,
so the same argument covers n=0; on the empty scheme all maps are unique. -/
theorem diagonalTrace_supportedFiniteBoundary_sourceStep
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : @Ext (DiagonalSystems l (diagonalSurface Y)) _ _
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      (D.E.obj (diagonalIntegralSource Y)) H 2)
    (hxi : @FiniteCartierNormalization l _ Y hY
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y)) D H roots xi)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (hs : SupportedSourceConeNormalization l Y D s)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (he : Functor.whiskerRight e.hom (diagonalForget l (diagonalSurface Y)) =
      roots.hom ≫ k.lineForget.inv)
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (hp : @ExtDerivedPresentation.Presents _ _ _
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      (DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y)) _ _ p xi)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) :
    ∃ a : SupportedFiniteBoundaryFrame l Y hY c r k n,
      supportedFiniteBoundaryCartierEquation l Y hY D H s c r k e p L₀ L n a := by
  unfold SupportedSourceConeNormalization at hs
  have hcoords := finiteCartierNormalization_coordinates l Y hY D H roots xi hxi n
  unfold FiniteCartierCoordinateNormalization at hcoords
  obtain ⟨sigma, t, hsigma, ht, hcycle⟩ := hcoords
  obtain ⟨a, ha, hcoeff⟩ := diagonalTrace_supportedFiniteBoundary_frame
    l Y hY c r k H roots e he n t ht
  have hf : HEq (diagonalCompletedGenerator l Y ≫
      (diagonalForget l (diagonalSurface Y)).map
        (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n) ≫ sigma.hom))
        (cartierProIntegralGenerator (diagonalResidue.{u} l n) (diagonalImmersion Y)) := by
    unfold DiagonalSourceNormalization at hsigma
    simpa only [Category.assoc] using (ordinarySourceGeneratorNormalization
      (diagonalForget l (diagonalSurface Y))
      (diagonalCompletedGenerator l Y)
      ((diagonalScalarAdjunction l (diagonalSurface Y)).unit.app
        (diagonalIntegralSource Y))
      (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n))
      ((D.π n).app (diagonalIntegralSource Y)) sigma.hom (hs n) _ hsigma)
  have hsource := diagonalTrace_supportedOrdinaryFiniteUnit l Y n
    (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n) ≫ sigma.hom)
    hf c r k a.coefficient hcoeff
  have hb := diagonalTrace_supportedFiniteCoordinateAssembly
    l Y hY D H xi s c r k e p hp L₀ L n a sigma t hsource hcycle
  rw [← ha] at hb
  exact ⟨a, diagonalTrace_supportedFiniteBoundary_of_coordinates
    l Y hY D H s c r k e p L₀ L n a hb⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
