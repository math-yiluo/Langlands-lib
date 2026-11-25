/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullback

/-! # Pullback of the complete diagonal coefficient family

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-family-pullback).

## Main definitions

- `QuotientPullMap`: the specified balanced-tensor formula.
- `FamilyPullback`: base change at every coefficient stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The quotient pullback map is fixed on every balanced tensor generator by
the coefficient pullback and the projection-normalized integral root map.
This definition also applies to ramified quotient levels outside the ell-power
cofinal subsystem. Source: blueprint clause 3 and proof step 3c
(blueprint: def-sfb-diagonal-coefficient-family-pullback). -/
def QuotientPullMap (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E) (n : ℕ)
    {X S : Scheme.{u}} (f : X ⟶ S)
    (m : (upperStar Ab.{u + 1} f).obj (quotientLine l E π n S).X ⟶
      (quotientLine l E π n X).X) : Prop :=
  (upperStar Ab.{u + 1} f).map
      (Mod.extendπ (coefficientMap (quotientMap l E π n) S) (spIntegralTwist S l E)) ≫ m =
    Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f)
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) S)
      (spIntegralTwist S l E).X ≫
    (condensedPullbackHom
        (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) f ⊗ₘ
      spIntegralComparison f l E) ≫
    Mod.extendπ (coefficientMap (quotientMap l E π n) X) (spIntegralTwist X l E)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
