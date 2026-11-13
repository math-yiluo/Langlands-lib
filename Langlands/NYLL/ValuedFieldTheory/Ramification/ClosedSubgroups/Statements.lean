/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 121, 2026-11-13: extract the type of the theorem M241.002
`decompositionGroup_isClosed` (line 57) of
`Nyll/ValuedFieldTheory/Ramification/ClosedSubgroups.lean` at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and package its complete elaborated telescope (section
variables of lines 32–33, then the theorem's own binder) as a closed
Prop-valued definition named with the suffix `Statement`. The NYLL import
`Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationGroup`
is replaced by the published M239 data module, which supplies the only NYLL
declaration used (`decompositionGroup`); `Mathlib.FieldTheory.Galois.Infinite`
is kept. The proof, the private helper M241.001 and all other declarations
are omitted.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions
import Mathlib.FieldTheory.Galois.Infinite

/-!
# finite Galois ramification theory: closedness of the decomposition group

Closed statement target for NYLL M241.002: for an algebraic extension `L / K`
the decomposition group of a valuation subring of `L` is closed in the Krull
topology on `L ≃ₐ[K] L`.
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- Statement target for NYLL M241.002 `decompositionGroup_isClosed`: the
valuation-subring decomposition group is closed in the Krull topology. -/
def decompositionGroup_isClosedStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (A : _root_.ValuationSubring L),
    IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L))

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
