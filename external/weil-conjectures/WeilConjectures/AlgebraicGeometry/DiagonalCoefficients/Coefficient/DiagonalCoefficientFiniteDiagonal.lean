/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientQuotientLine

/-! # Canonical finite diagonal class and trace comparison

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-finite-diagonal).

## Main definitions

- `FiniteDiagonalComparison`: the actual Cartier class and unit/Chern trace equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The existing canonical Cartier Ext class as its actual derived arrow.
Source: blueprint clause 1, positive Cartier normalization
(blueprint: def-sfb-diagonal-coefficient-finite-diagonal). -/
def finiteCartierArrow (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤))) :
    (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
          (geoCartierConstant A (ProjectiveLine Y))) ⟶
    ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).obj
        (geoCartierLine A N hA (diagonalSurface Y)))⟦(2 : ℤ)⟧ :=
  SpTowerClasses.extensionArrow (geoCartierCanonicalClass A N hN hA (diagonalImmersion Y)
    (diagonalImmersion_cartier Y) hW)

/-- A finite diagonal comparison uses the canonical Cartier arrow, and its trace
is the inverse of the positive unit/Chern splitting followed by the constant
summand projection. Both comparisons retain the actual coefficient units and the
full universal derived units. Source: blueprint clause 1 and proof step 1
(blueprint: def-sfb-diagonal-coefficient-finite-diagonal). -/
def FiniteDiagonalComparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (A : Type (u + 1)) [CommRing A] [hfinite : Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (N : Γ(Y, ⊤))) (hW : IsUnit (N : Γ(diagonalSurface Y, ⊤)))
    (L : ∀ X : Scheme.{u}, Modules R X) (d : Diagram R Y L)
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (eW : FiniteRealization R A (diagonalSurface Y))
    (lineP : eP.F.obj (L (ProjectiveLine Y)) ≅ geoCartierLine A N hA (ProjectiveLine Y))
    (lineW : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y)) : Prop :=
  ∃ sourceIso : eW.F.obj
      (source R Y) ≅
    (lowerStar (ModuleCat.{u + 1} A)
      (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)),
  (HEq (eW.underlying.inv.app
        (source R Y) ≫
      (sheafCompose (Scheme.ProEt.topology (diagonalSurface Y))
        (forget₂ (ModuleCat.{u + 1} A)
          Ab.{u + 1})).map sourceIso.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (Mod.regular (condensedRingObj
          R (ProjectiveLine Y))) ≫
          (sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
            (forget₂ (ModuleCat.{u + 1} A)
              Ab.{u + 1})).map eP.unitIso.hom))) ∧
  ((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
        sourceIso.inv ≫
      SpTowerClasses.mapSingleArrow eW.F (X := source R Y)
        (Y := L (diagonalSurface Y)) (2 : ℤ) d.delta ≫
        ((DerivedCategory.singleFunctor
          (Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) (ModuleCat.{u + 1} A)) 0).map
            lineW.hom)⟦(2 : ℤ)⟧' =
    finiteCartierArrow A N hN hA Y hW) ∧
  ∃ (Rq : DiagonalRightDerived
    (lowerStar (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)))
    (q_canonical : Rq.R = geoP1Pushforward A
    (ProjectiveLine Y ↘ Y)),
  IsCanonicalRightDerived
    (lowerStar (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)) Rq q_canonical ∧
  ∃ (q_square : FinitePushSquare
    R
    A (ProjectiveLine Y ↘ Y) eP eY d.Rq Rq)
    (splitting : (geoP1Twist A N hA Y 1 2 ⊞
      geoP1Unit A Y) ≅
    (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).obj
      (geoP1Twist A N hA
        (ProjectiveLine Y) 1 2)),
  (splitting.hom =
    geoP1TwistedMap A N
      hN hA Y hY) ∧
  eY.F.mapDerivedCategory.map d.traceq ≫ eY.derivedUnit =
    q_square.derived.iso.hom.app _ ≫ Rq.R.map (eP.shiftedLine N hA (L (ProjectiveLine Y)) lineP) ≫
      (eqToIso q_canonical).hom.app _ ≫
        geoP1Trace A N hA Y splitting

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
