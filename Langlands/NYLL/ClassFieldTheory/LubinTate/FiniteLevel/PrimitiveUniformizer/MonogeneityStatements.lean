/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 298, 13 November 2026: extract source M346.001–002 as
Prop-valued public targets; adapt namespace and imports; omit source proofs.
Original private names correspond to PortInternal.M346.d001Statement/d002Statement.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-! # Eisenstein monogeneity targets for the standard Lubin--Tate route -/

namespace Langlands.NYLL.PortInternal.M346

set_option linter.unusedVariables false in
def d001Statement
    {R K' L : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K'] [Field L]
    [Algebra R K'] [Algebra K' L] [Algebra R L]
    [IsScalarTower R K' L] [IsFractionRing R K']
    [FiniteDimensional K' L] [Algebra.IsSeparable K' L]
    (B : PowerBasis K' L) (pi : R) (hpi : Irreducible pi)
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R)))
    {z : L} (hzint : IsIntegral R z) : Prop :=
    z ∈ Algebra.adjoin R ({B.gen} : Set L)

set_option linter.unusedVariables false in
def d002Statement
    {R K' L A : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K'] [Field L] [CommRing A]
    [Algebra R K'] [Algebra K' L] [Algebra R L]
    [Algebra R A] [Algebra A L]
    [IsScalarTower R K' L] [IsScalarTower R A L]
    [IsFractionRing R K'] [FiniteDimensional K' L]
    [Algebra.IsSeparable K' L] [IsIntegralClosure A R L]
    (B : PowerBasis K' L) (pi : R) (hpi : Irreducible pi)
    (a : A) (ha : algebraMap A L a = B.gen)
    (hmap_injective : Function.Injective (algebraMap A L))
    (hBint : IsIntegral R B.gen)
    (hei : (minpoly R B.gen).IsEisensteinAt
      (Ideal.span ({pi} : Set R))) : Prop :=
    Algebra.adjoin R ({a} : Set A) = ⊤

end Langlands.NYLL.PortInternal.M346
