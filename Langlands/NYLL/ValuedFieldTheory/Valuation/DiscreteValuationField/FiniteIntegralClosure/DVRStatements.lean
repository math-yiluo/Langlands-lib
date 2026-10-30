/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 764 (2026-10-30): extract only the statements of
M245.010 (FiniteIntegralClosure.lean, lines 309-314, keeping its
omit [FiniteDimensional K L] clause) and M245.011 (lines 331-334), with the
universe and variable context of lines 23 and 30-31, from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued definitions
with explicit independent universe parameters; prefix the namespace with
Langlands.NYLL; rename the targets; unfold the source abbreviation
base.valuationSubring to the actual valuation subring; reword the M245.010
docstring, which says "nontrivial finite" although the statement assumes
neither; import the public CompleteDVF definition and focused Mathlib
modules. The original theorem proofs and the other source declarations are
not included. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Mathlib.Algebra.Field.IsField
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Integral closures over complete DVFs: not a field, and a DVR

These closed propositions state NYLL M245.010 and M245.011 with every type,
structure, chosen complete discrete valuation and hypothesis quantified inside
the body. Only universe levels are declaration parameters, and the field,
value-group and extension universes are independent. They state the original
conclusions about the actual integral closure of the base valuation subring
without proving them. As in the source, the first statement assumes a
separable extension but not a finite one; the second also assumes
finite dimensionality.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- In a separable extension `L` of a field `K` with a chosen complete discrete
valuation, the actual integral closure of the valuation subring in `L` is not
a field. Finite dimensionality and nontriviality of the extension are not
assumed. This is a proposition target, not a proof. -/
def IntegralClosureNotIsFieldOfFiniteSeparableStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    ¬ IsField (integralClosure base.valuation.valuationSubring L)

/-- In a finite separable extension `L` of a field `K` with a chosen complete
discrete valuation, the actual integral closure of the valuation subring in `L`
is a discrete valuation ring. This is a proposition target, not a proof. -/
def IntegralClosureIsDiscreteValuationRingOfFiniteSeparableStatement.{u, v, w} :
    Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    IsDiscreteValuationRing (integralClosure base.valuation.valuationSubring L)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
