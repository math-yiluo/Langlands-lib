/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryEquation

/-! # Assembly of the finite Cartier and Chern endpoint equations -/

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
  completedSupportedUnit

private theorem supportedBoundaryEquation_replace
    {A C B : Type*} [Category A] [Category C] [Category B]
    {U : A ⥤ B} {R V : C ⥤ B} {pi : R ⟶ V}
    {P Q : A} {K J W : C} {g : P ⟶ Q} {t : U.obj Q ⟶ R.obj K}
    {f : K ⟶ J} {b : J ⟶ W} {x y : U.obj P ⟶ V.obj W}
    (h : supportedBoundaryEquation U R V pi g t f b x) (hx : x = y) :
    supportedBoundaryEquation U R V pi g t f b y := by
  cases hx
  exact h

/-- Transport the fixed finite Cartier boundary equation along its Chern comparison.
This is only equation assembly: it has no finite-cycle or Chern normalization
hypotheses and adds no mathematical obligation.

Source: diagonal trace proof (2), combination of the finite source and target equations.
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-combination).

Proof: unfold the two named boundary predicates, which have identical source,
presentation and root comparisons. Transport the endpoint of the supported
boundary equation along ht using the generic equation-transport lemma. -/
theorem diagonalTrace_supportedFiniteBoundary_combine
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ)
    (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (hs : supportedFiniteBoundaryCartierEquation l Y hY D H s c r k e p L₀ L n a)
    (ht : a.cartierMap l Y hY c r k n L
      (cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
        (diagonalImmersion Y) (diagonalImmersion_cartier Y)
        (diagonalSurface_power_unit l Y hY n)) =
      finiteChernComposite l (diagonalSurface Y) c r k L n
        (SpTowerClasses.diagonalPic Y)) :
    finiteBoundaryEquation l Y D H p s c r k e L₀ L n := by
  unfold supportedFiniteBoundaryCartierEquation at hs
  unfold finiteBoundaryEquation
  exact supportedBoundaryEquation_replace hs ht

end AlgebraicGeometry.ProEtale.DiagonalTrace
