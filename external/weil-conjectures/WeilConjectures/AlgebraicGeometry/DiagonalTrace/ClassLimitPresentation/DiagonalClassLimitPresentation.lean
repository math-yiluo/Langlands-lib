/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

/-! # The normalized limit data used in diagonal pullback

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

/-- The `Ext` structure on strict systems over the diagonal surface, as a constant applied to
variables. Instance search through the class projection `DiagonalTraceLocalizations.ext` at
`diagonalSurface Y` produces an auxiliary proof whose statement the kernel only matches against
`HasExt` by unfolding derived categories, in every declaration generated for the structure. -/
abbrev diagonalSurfaceSystemsHasExt (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [i : DiagonalTraceLocalizations l (diagonalSurface Y)] :
    HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y)) :=
  i.ext

attribute [local instance high] diagonalSurfaceSystemsHasExt

/-- Named fields for the whole-system data of the diagonal limit. This structure
chooses no witnesses and imposes no new property on the completed class.

Source: the defining predicate `IsDiagonalLimit`, blueprint coefficient proof (3).
(blueprint: def-diagonal-class-limit-presentation). -/
structure ClassLimitPresentation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))) where
  H : DiagonalSystems l (diagonalSurface Y)
  roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
    Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime)
  a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
    (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y))
  b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
    (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧
  c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2
  a_normalization : a.hom = diagonalDerivedSingleCounit l
    (diagonalScalarExtension l (diagonalSurface Y)) D (diagonalIntegralSource Y)
  boundary_normalization : c.hom =
    a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom
  finite_normalization : FiniteCartierNormalization l Y hY D.ordinary H roots c
  L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))
  s₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (diagonalCompletedSource l Y) ≅
    limit (D.ordinary.E.obj (diagonalIntegralSource Y))
  t₀ : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H
  source_normalization : ∀ n : ℕ,
    diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
      (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
    (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
      (diagonalForget l (diagonalSurface Y)).map
        ((D.ordinary.π n).app (diagonalIntegralSource Y))
  target_normalization : HEq ((diagonalForget l (diagonalSurface Y)).map t₀.hom)
    (diagonalRootLimitComparison l (diagonalSurface Y) H roots).inv
  source_isIso : IsIso (diagonalSingleLimitComparison
    (diagonalCompletedRestriction l (diagonalSurface Y)) L
    (diagonalCompletedSource l Y) _ _ s₀ a)
  target_isIso : IsIso (diagonalShiftedSingleLimitComparison
    (diagonalCompletedRestriction l (diagonalSurface Y)) L
    (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ t₀ b)
  unique : ∃! δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
    (diagonalCompletedUnderlying l (diagonalSurface Y)).map δ ≫
        diagonalShiftedSingleLimitComparison
          (diagonalCompletedRestriction l (diagonalSurface Y)) L
          (Scheme.purTwistZlModule (diagonalSurface Y) l) _ _ t₀ b =
      diagonalSingleLimitComparison
          (diagonalCompletedRestriction l (diagonalSurface Y)) L
          (diagonalCompletedSource l Y) _ _ s₀ a ≫
        L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)

end AlgebraicGeometry.ProEtale.DiagonalTrace
