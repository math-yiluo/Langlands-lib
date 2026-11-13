/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 329, 2026-11-13: extract only the signature of M397.001
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as a closed
Prop-valued definition; prefix namespaces with Langlands.NYLL, reuse the
published valuation-ring automorphism, and narrow the import to its module.
Preserve the four independent universes and both source hypotheses.
The source proof is omitted. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut

/-!
# The valuation-theoretic Krasner stabilizer step: statement

This is the signature of M397.001, lines 45–62 of the pinned
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationKrasner.lean`,
with its section parameters quantified inside a proposition.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- Under unique valuation extension, an automorphism fixing `b` fixes `a` if
every nonzero displacement of `a` has strictly smaller additive valuation
than `a - b`. -/
def valuationSubringAutOfUniqueExtension_eq_of_fixed_of_closeStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (σ : Gal(L/K)) (a b : target.valuationSubring)
    (hfix :
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ b = b)
    (hclose :
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a ≠ a →
        IsDiscreteValuationRing.addVal target.valuationSubring
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) <
          IsDiscreteValuationRing.addVal target.valuationSubring
            (a - b)),
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a = a

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
