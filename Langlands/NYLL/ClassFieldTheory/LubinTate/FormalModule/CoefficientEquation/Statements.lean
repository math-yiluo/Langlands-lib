/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 485, 2026-11-14: extract the signatures of M337.001–004
and M337.006 (lines 34, 41, 53, 60 and 79) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets named
`<source name>Statement`; prefix the namespace and the opened namespace with
Langlands.NYLL; replace the source Series import by the published LocalField
definition module, which the signatures alone use; drop the source imports
Mathlib.Algebra.Group.Units.Basic and Mathlib.Logic.Function.Basic, used only
by the omitted proofs and by M337.005; underscore unused hypothesis names;
omit M337.005, all proofs and the unused noncomputable section; replace the
module documentation and docstrings.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-!
# Targets for the fixed-uniformizer coefficient equation

This module states five theorems of
`Nyll/ClassFieldTheory/LubinTate/FormalModule/CoefficientEquation.lean`:
a uniformizer and its nonzero powers reduce to zero, an element with zero
residue is divisible by the uniformizer, `1 - π ^ r` is a unit for `r ≠ 0`,
and the scalar equation `(1 - π ^ r) * x = b` has a unique solution in the
valuation subring. It contains proposition definitions only.
-/

universe u v

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Target for M337.001: a chosen uniformizer reduces to zero in the residue
field. -/
def residueMap_uniformizer_eq_zeroStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) : Prop :=
  F.residueMap π = 0

/-- Target for M337.002: an element reducing to zero is divisible by the
chosen uniformizer. -/
def uniformizer_dvd_of_residueMap_eq_zeroStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {a : F.valuationSubring} (_ha : F.residueMap a = 0) : Prop :=
  π ∣ a

/-- Target for M337.003: every nonzero power of a uniformizer reduces to
zero. -/
def residueMap_uniformizer_pow_eq_zeroStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (_hr : r ≠ 0) : Prop :=
  F.residueMap (π ^ r) = 0

/-- Target for M337.004: for `r ≠ 0`, the factor `1 - π ^ r` is a unit of the
valuation subring. -/
def isUnit_one_sub_uniformizer_powStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (_hr : r ≠ 0) : Prop :=
  IsUnit (1 - π ^ r)

/-- Target for M337.006: for `r ≠ 0`, the scalar coefficient equation
`(1 - π ^ r) * x = b` has a unique solution in the valuation subring. -/
def existsUnique_one_sub_uniformizer_pow_mul_eqStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    {r : ℕ} (_hr : r ≠ 0) (b : F.valuationSubring) : Prop :=
  ∃! x : F.valuationSubring, (1 - π ^ r) * x = b

end Langlands.NYLL.LubinTate.SameUniformizer
