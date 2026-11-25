/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback

/-! # Ordinary quotient endpoints under geometric pullback

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-source-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

/-- Extension of the integral source and line comparisons to an ordinary quotient.
No class, trace, right derived model, or scalar compatibility is used here.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), coefficient functors
commuting with pullback; original quotient-base-change proof, step 1.
(blueprint: lem-diagonal-quotient-source-pullback).

Proof: Write a for the condensed quotient coefficient map. The coefficient square
for inverse image commutes by naturality of condensedPullbackHom. The ordinary
scalar/pullback compositor, obtained by conjugating comapLowerStarIso, therefore
identifies pullback of extension of scalars with extension of module pullback.
Extend the two integral line isomorphisms through this compositor. Transposing
their module maps through the ordinary geometric adjunction gives mP and mW.
On the defining coequalizers of extension of scalars, the compositor sends a
coefficient tensor a root to the pulled-back coefficient tensor the integral
root comparison. Naturality of extendUnit and the normalization of the two
integral PullEndpoints give precisely the two QuotientPullMap equations.
The coefficient-unit comparisons are the regular-module pullbacks. The diagonal
square is cartesian. Closed base change on abelian sheaves, with its coefficient
module structure, identifies the ordinary supported quotient source with the
source on the new base. Its Hom-adjoint is the unit followed by the diagonal
counit, which is exactly ordinaryExchange followed by the coefficient-unit map.
Use this isomorphism as supported and this adjunction computation as its
supported_normalization; retain the three original geometric square equations.
All constructions are ordinary tensor constructions, so no flatness or regularity
of the quotient is required, including pi = 0 or a unit. -/
theorem diagonalQuotient_sourcePullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (s : SourcePullback (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)) :
    ∃ (mP : (upperStar Ab.{u + 1} (baseP g)).obj
        (quotientLine l E π n (ProjectiveLine Y)).X ⟶
          (quotientLine l E π n (ProjectiveLine Y')).X)
      (mW : (upperStar Ab.{u + 1} (baseW g)).obj
        (quotientLine l E π n (diagonalSurface Y)).X ⟶
          (quotientLine l E π n (diagonalSurface Y')).X),
      QuotientPullMap l E π n (baseP g) mP ∧
      QuotientPullMap l E π n (baseW g) mW ∧
      Nonempty (SourcePullback
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
        (quotientLine l E π n) mP mW) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
