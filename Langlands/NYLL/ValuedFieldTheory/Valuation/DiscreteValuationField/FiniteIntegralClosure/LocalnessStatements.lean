/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 764 (2026-10-28): extract only the statements of
M245.005 (FiniteIntegralClosure.lean, lines 122-127) and M245.006
(lines 183-186), with the universe and variable context of lines 23 and
30-31, from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued definitions
with explicit independent universe parameters; prefix the namespace with
Langlands.NYLL; rename the targets; unfold the source abbreviations
base.valuationSubring and base.maximalIdeal to the actual valuation subring
and its maximal ideal; import the public CompleteDVF definition and focused
Mathlib modules. The original theorem proofs and the other source
declarations are not included. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Fiber uniqueness and localness of finite integral closures

These closed propositions state NYLL M245.005 and M245.006 with every type,
structure, chosen complete discrete valuation and hypothesis quantified inside
the body. Only universe levels are declaration parameters, and the field,
value-group and extension universes are independent. They state the original
conclusions about the actual integral closure of the base valuation subring in
a finite separable extension without proving them.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- In a finite separable extension `L` of a field `K` with a chosen complete
discrete valuation, the residue fiber of the actual integral closure of the
valuation subring over its maximal ideal has at most one prime. This is a
proposition target, not a proof. -/
def IntegralClosureBaseMaximalFiberSubsingletonOfFiniteSeparableStatement.{u, v, w} :
    Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    Subsingleton
      (PrimeSpectrum
        ((IsLocalRing.maximalIdeal base.valuation.valuationSubring).Fiber
          (integralClosure base.valuation.valuationSubring L)))

/-- In a finite separable extension `L` of a field `K` with a chosen complete
discrete valuation, the actual integral closure of the valuation subring in `L`
is a local ring. This is a proposition target, not a proof. -/
def IntegralClosureIsLocalRingOfFiniteSeparableStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    IsLocalRing (integralClosure base.valuation.valuationSubring L)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
