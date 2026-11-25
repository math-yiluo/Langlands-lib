/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteOrdinaryComparisons

/-! # Finite normalization equations at generic coefficients

The two predicates name the separate arrow equalities in `FiniteDiagonalComparison`.
Generic coefficient parameters keep their types small.
Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: def-diagonal-finite-arrow-equations).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R] (A : Type (u + 1)) [CommRing A]

/-- The Cartier-arrow equality with its source and line isomorphisms supplied.
Source: coefficient changes (blueprint: def-diagonal-finite-arrow-equations). -/
@[irreducible]
def FiniteCartierArrowEquation [Finite A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eW : FiniteRealization R A (diagonalSurface Y))
    (lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (sourceIso : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y))) : Prop :=
  (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
      sourceIso.inv ≫ SpTowerClasses.mapSingleArrow eW.F
        (X := source R Y) (Y := L (diagonalSurface Y)) (2 : ℤ) d.delta ≫
      ((DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
          lineW.hom)⟦(2 : ℤ)⟧' = finiteCartierArrow A N hN hA Y hW

/-- The projective-line trace equality with its full-unit square and splitting supplied.
Source: coefficient changes (blueprint: def-diagonal-finite-arrow-equations). -/
@[irreducible]
def FiniteProjectiveTraceEquation (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (Rq : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (q_canonical : Rq.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (q_square : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY d.Rq Rq)
    (splitting : (geoP1Twist A N hA Y 1 2 ⊞ geoP1Unit A Y) ≅
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
        (geoP1Twist A N hA (ProjectiveLine Y) 1 2)) : Prop :=
  eY.F.mapDerivedCategory.map d.traceq ≫ eY.derivedUnit =
    q_square.derived.iso.hom.app _ ≫
      Rq.R.map (eP.shiftedLine N hA (L (ProjectiveLine Y)) lineP) ≫
        (eqToIso q_canonical).hom.app _ ≫ geoP1Trace A N hA Y splitting

/-- Supplied finite right-derived model, normalized square and positive splitting.
Source: coefficient changes (blueprint: def-diagonal-finite-arrow-equations). -/
structure FiniteTracePresentation [Finite A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y)) where
  Rq : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
  q_canonical : Rq.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y)
  hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) Rq q_canonical
  q_square : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY d.Rq Rq
  splitting : (geoP1Twist A N hA Y 1 2 ⊞ geoP1Unit A Y) ≅
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
        (geoP1Twist A N hA (ProjectiveLine Y) 1 2)
  hsplitting : splitting.hom = geoP1TwistedMap A N hN hA Y hY

/-- The same trace equality, with projections kept at generic coefficients.
Source: coefficient changes (blueprint: def-diagonal-finite-arrow-equations). -/
@[irreducible]
def FinitePresentedTraceEquation [Finite A] (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (L : ∀ X : Scheme.{u}, Modules R X)
    (d : Diagram R Y L) (eY : FiniteRealization R A Y)
    (eP : FiniteRealization R A (ProjectiveLine Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP) : Prop :=
  FiniteProjectiveTraceEquation R A N hA Y L d eY eP lineP
    p.Rq p.q_canonical p.q_square p.splitting

/-- Assemble the separate normalized class and trace equations into the existing predicate.
Source: coefficient changes (blueprint: lem-diagonal-finite-comparison-assembly).
Proof: unfold the two equation predicates and insert their witnesses and equalities
into the definition of FiniteDiagonalComparison. No comparison data are chosen. -/
theorem finiteDiagonalComparison_of_equations [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (sourceComparison : FiniteSourceComparison R A Y eP eW)
    (p : FiniteTracePresentation R A N hN hA Y hY L d eY eP)
    (hclass : FiniteCartierArrowEquation R A N hN hA Y hW L d eW lineW
      sourceComparison.iso)
    (htrace : FinitePresentedTraceEquation R A N hN hA Y hY L d eY eP lineP p) :
    FiniteDiagonalComparison R A N hN hA Y hY hW L d eY eP eW lineP lineW := by
  unfold FiniteCartierArrowEquation at hclass
  unfold FinitePresentedTraceEquation FiniteProjectiveTraceEquation at htrace
  unfold FiniteDiagonalComparison
  exact ⟨sourceComparison.iso, sourceComparison.normalization, hclass,
    p.Rq, p.q_canonical, p.hcanonical, p.q_square, p.splitting, p.hsplitting, htrace⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
