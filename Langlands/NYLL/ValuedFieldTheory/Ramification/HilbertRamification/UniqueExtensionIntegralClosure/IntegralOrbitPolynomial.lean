/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 556, 2026-11-14: isolate M308.001 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, narrow imports to the published valuation-ring automorphism
and Mathlib polynomial data, and retain only the actual declaration parameters.
Keep classical selection local. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut
import Mathlib.Algebra.Polynomial.Basic

/-!
# The full integral-orbit polynomial

This isolates M308.001, lines 44–52 of the pinned
`UniqueExtensionIntegralClosure.lean`. It is the product over all algebra
automorphisms, with coefficients in the actual chosen target valuation ring.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [FiniteDimensional K L] [base.valuation.HasExtension target.valuation]

/-- The full Galois-orbit polynomial of an element of the chosen target
valuation ring, retaining a factor for every algebra automorphism. -/
noncomputable def integralOrbitPolynomial
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (a : target.valuationSubring) : Polynomial target.valuationSubring := by
  classical
  exact ∏ σ : Gal(L/K),
    (Polynomial.X - Polynomial.C
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a))

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
