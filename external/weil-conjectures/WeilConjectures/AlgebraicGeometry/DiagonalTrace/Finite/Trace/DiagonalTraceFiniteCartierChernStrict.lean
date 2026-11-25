/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedSupportedUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceConeNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceExtPresentation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteChernEquation

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceNormalizedRootCone
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceNormalizedRootIso
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRootProjection
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundary

/-! # The finite Chern equation from an explicit strict presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

private theorem combine_projection
    {C S V : Type*} [Category C] [Category S] [Category V]
    {U : C ⥤ V} {R ev : S ⥤ V} {pi : R ⟶ ev}
    {W X Y : C} {A B T : S}
    {g : W ⟶ X} {d : X ⟶ Y} {a : U.obj X ⟶ R.obj A}
    {b : U.obj Y ⟶ R.obj B} {f : A ⟶ B} {t : B ⟶ T}
    {v : U.obj W ⟶ ev.obj T} {z : U.obj Y ⟶ ev.obj T}
    (hd : U.map d ≫ b = a ≫ R.map f)
    (hb : rootProjectionEquation R ev pi b t z)
    (hc : supportedBoundaryEquation U R ev pi g a f t v) :
    completedBoundaryEquation U g d z v := by
  unfold completedBoundaryEquation
  unfold rootProjectionEquation at hb
  unfold supportedBoundaryEquation at hc
  rw [← hb, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hd, reassoc_of% pi.naturality f]
  exact hc

/-- The finite Chern calculation from its explicit strict-system presentation.
This proved interface keeps existential elimination separate from the comparison
calculation, so their concrete category types are checked independently.

Source: diagonal trace proof (1)--(2), projecting the strict Cartier class.
(blueprint: lem-sfb-diagonal-trace-finite-cartier-chern-strict).

Proof: construct the normalized linear root isomorphism and identify its ordinary
cone. Its finite root-projection equation transports the target to the Chern line.
Precompose the given whole-system equation by the supported unit, then project.
Naturality moves the strict presentation arrow across the projection. The finite
supported Cartier/Chern equation identifies the resulting composite. -/
theorem diagonalTrace_finiteCartierChern_strict
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : CategoryTheory.Abelian.Ext (D.E.obj (diagonalIntegralSource Y)) H 2)
    (hfinite : FiniteCartierNormalization l Y hY D H roots xi)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (hs : SupportedSourceConeNormalization l Y D s)
    (t : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (ht : HEq ((diagonalForget l (diagonalSurface Y)).map t.hom)
      (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv)
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (hn : c.Normalized l (ULift.{u} (Padic l)))
    (hc : SpTowerClasses.FiniteChernNormalization l (ULift.{u} (Padic l)) c)
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (hp : p.Presents xi)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ)
    (hwhole : (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫
        diagonalShiftedSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
          L₀ (Scheme.purTwistZlModule (diagonalSurface Y) l) H p.J t p.target =
      diagonalSingleLimitComparison (diagonalCompletedRestriction l (diagonalSurface Y))
          L₀ (diagonalCompletedSource l Y) (D.E.obj (diagonalIntegralSource Y)) p.K s p.source ≫
        L₀.R.map p.arrow) :
    finiteChernEquation l Y c r k L n δ := by
  let e := diagonalTraceNormalizedRootIso l (diagonalSurface Y) c r k H roots
  have he := whiskerRight_diagonalTraceNormalizedRootIso_hom l (diagonalSurface Y) c r k H roots
  have hcone := diagonalTrace_normalizedRootCone l (diagonalSurface Y)
    c r k H roots t ht e he
  have hprojection := diagonalTrace_rootProjection l (diagonalSurface Y)
    c r k H _ p.target t e hcone L₀ L n
  have hboundary := diagonalTrace_supportedFiniteBoundary l Y hY D
    H roots xi hfinite s hs c hn hc r k e he p hp L₀ L n
  unfold finiteBoundaryEquation supportedSourceComparison extSourceComparison
    at hboundary
  dsimp only at hboundary
  unfold finiteChernEquation
  dsimp only
  exact combine_projection hwhole hprojection hboundary

end AlgebraicGeometry.ProEtale.DiagonalTrace
