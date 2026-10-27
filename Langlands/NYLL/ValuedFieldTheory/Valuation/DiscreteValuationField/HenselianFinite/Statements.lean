/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 785 (2026-10-27): extract only the statements of
M105.001 (AdicPower.lean, lines 22-30) and M191.014 (HenselianFinite.lean,
lines 25 and 261-266) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as closed Prop-valued definitions
with explicit independent universe parameters; prefix the namespace with
Langlands.NYLL; rename the targets; use focused Mathlib-only imports.
The original theorem proofs, M191.013 and the other source declarations are
not included. The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Adic completeness under linear equivalence and for finite modules

These closed propositions state NYLL M105.001 and M191.014 with every type,
structure, ideal, equivalence and hypothesis quantified inside the body.
Only universe levels are declaration parameters, and the ring and module
universes are independent. They state the original conclusions without
proving them.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- Adic completeness is preserved by a linear equivalence of modules over the
same base ring and with respect to the same ideal. This is a proposition
target, not a proof. -/
def IsAdicCompleteOfLinearEquivStatement.{u, v, w} : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R) (_e : M ≃ₗ[R] N) [IsAdicComplete I M],
    IsAdicComplete I N

/-- A finite module over a Noetherian ring that is adically complete for an
ideal is adically complete for the same ideal. This is a proposition target,
not a proof. -/
def IsAdicCompleteOfModuleFiniteStatement.{u, v} : Prop :=
  ∀ (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [IsNoetherianRing R] [Module.Finite R M]
    [IsAdicComplete I R],
    IsAdicComplete I M

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
