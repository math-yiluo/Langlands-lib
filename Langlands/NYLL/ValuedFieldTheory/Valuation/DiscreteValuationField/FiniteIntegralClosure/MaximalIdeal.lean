/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 1045 (2026-10-30): extract only the definition
M245.007 (FiniteIntegralClosure.lean, lines 253-262), with the universe and
variable context of lines 23 and 30-31, from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; write the ambient variables as binders of the definition with
explicit independent universe parameters u, v, w; expand the source
abbreviation base.valuationSubring to the actual valuation subring
base.valuation.valuationSubring; apply the published M245.006 theorem, whose
statement is a closed proposition, to K, L and base explicitly. Replace
upstream imports by the published localness proof and a focused Mathlib
import. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.LocalnessProof
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# The maximal ideal of a finite integral closure

The only definition names NYLL M245.007: the maximal ideal of the actual
integral closure of the valuation subring of a complete DVF in a finite
separable extension, for the local ring structure given by the accepted
M245.006 theorem.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The maximal ideal of the integral closure, using the finite
separable localness theorem M245.006. -/
noncomputable def CanonicalIntegralClosure.maximalIdeal.{u, v, w}
    {K : Type u} {L : Type w} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L]
    (base : CompleteDVF.{u, v} K)
    [Algebra.IsSeparable K L] :
    Ideal (integralClosure base.valuation.valuationSubring L) :=
  letI : IsLocalRing (integralClosure base.valuation.valuationSubring L) :=
    integralClosure_isLocalRing_of_finite_separable.{u, v, w} K L base
  IsLocalRing.maximalIdeal (integralClosure base.valuation.valuationSubring L)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
