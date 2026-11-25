/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierArrowCoordinateHom
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteCoordinateEquation

/-! # Assembling the finite coordinate equation -/

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

/-- Assemble the finite coordinate equation from the ordinary source-unit equation
and the normalized finite Ext equation.
Source: diagonal trace proof (2), finite source projection.
(blueprint: lem-sfb-diagonal-trace-supported-finite-coordinate-assembly).

Proof: specialize diagonalTrace_finiteBoundary_of_ordinaryUnit to the completed
restriction, the chosen coefficient system, and the two normalized finite coordinates.
The named finiteCartierArrow is the Hom of the finite Cartier class. The source,
root, and exact-single comparisons in supportedFiniteCoordinateEquation are exactly
these specialized abstract comparisons. No source normalization or existence of
coordinates is assumed or constructed here. -/
theorem diagonalTrace_supportedFiniteCoordinateAssembly
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (xi : @Ext (DiagonalSystems l (diagonalSurface Y)) _ _
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      (D.E.obj (diagonalIntegralSource Y)) H 2)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (hp : @ExtDerivedPresentation.Presents _ _ _
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      (DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y)) _ _ p xi)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ)
    (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (sigma : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
      finiteCartierSourceObject l Y n)
    (t : H.obj (op n) ≅ finiteCartierLineObject l Y n)
    (hsource : (diagonalCompletedRestriction l (diagonalSurface Y)).map
        (completedSupportedUnit l Y) ≫ s.hom ≫
        limit.π (D.E.obj (diagonalIntegralSource Y)) (op n) ≫ sigma.hom =
      k.coefficientProjection.app (op n) ≫ a.coefficient.hom ≫
        (diagonalFiniteToPadic l n (diagonalSurface Y)).map
          (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
            (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))))
    (hcycle : @normalizedFiniteExtClass (DiagonalMod l (diagonalSurface Y))
      (inferInstanceAs (Category (DiagonalMod l (diagonalSurface Y))))
      (inferInstanceAs (Abelian (DiagonalMod l (diagonalSurface Y))))
      (DiagonalCoefficients.cyclicCoefficientHasExt l (diagonalSurface Y))
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      _ _ xi n _ _ sigma t = finiteCartierCoordinateClass l Y hY n) :
    supportedFiniteCoordinateEquation l Y hY D H s c r k e p L₀ L n a
      (e.symm.app (op n) ≪≫ t) := by
  unfold supportedFiniteCoordinateEquation
  exact @diagonalTrace_finiteBoundary_of_ordinaryUnit
    (DiagonalCompleted l (diagonalSurface Y)) (DiagonalMod l (diagonalSurface Y))
    (SpTowerClasses.Systems (diagonalSurface Y)
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
    _ (inferInstanceAs (Category (DiagonalMod l (diagonalSurface Y)))) _
    _ (inferInstanceAs (Abelian (DiagonalMod l (diagonalSurface Y)))) _
    (DiagonalTraceLocalizations.completed (ℓ := l) (X := diagonalSurface Y))
    (DiagonalTraceLocalizations.mod (ℓ := l) (X := diagonalSurface Y))
    (Scheme.ProjectionRestriction.derived
      (WeilConjectures.SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology (diagonalSurface Y))
        (fun j ↦ (SpTowerClasses.Arings l (ULift.{u} (Padic l))
          (diagonalSurface Y)).obj (op j))
        (fun j ↦ (SpTowerClasses.Arings l (ULift.{u} (Padic l))
          (diagonalSurface Y)).map (homOfLE (Nat.le_succ j)).op)))
    (DiagonalTraceLocalizations.systems (ℓ := l) (X := diagonalSurface Y))
    _ (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
    (DiagonalCoefficients.cyclicCoefficientHasExt l (diagonalSurface Y))
    (diagonalCompletedRestriction l (diagonalSurface Y)) _ _ _ r.F _ _ _
    _ _ (completedSupportedUnit l Y) _ _ xi p hp s L₀ L
    (SpTowerClasses.coefficient (diagonalSurface Y)
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
    (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c) e n _ _ _
    a.coefficient sigma t
    k.coefficientProjection
    ((diagonalFiniteToPadic l n (diagonalSurface Y)).map
      (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
        (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))))
    (finiteCartierCoordinateClass l Y hY n) hsource hcycle
    (finiteCartierArrow l Y hY n) (finiteCartierArrow_coordinate_hom l Y hY n).symm

end AlgebraicGeometry.ProEtale.DiagonalTrace
