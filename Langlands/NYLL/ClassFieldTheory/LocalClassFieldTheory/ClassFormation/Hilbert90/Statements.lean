/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Hilbert 90 and negative Tate cohomology of field units: target

Modified by Worker 5454: extract the asserted type of M115.001
`LocalClassFieldTheory.unitsTateHminusOne_card_eq_one` from the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Hilbert90.lean`
(lines 24–30) as a Prop-valued definition. Prefix the namespace with
`Langlands.NYLL`, append `Statement` to the theorem name, keep every source
parameter in order and binder kind, and omit the proof. The source's Mathlib
import is kept and its NYLL import is replaced by the two Mathlib modules that
state the target (unit representation and Tate cohomology); the eventual proof
will also import the M112 data module of this port. The source's
`open CyclicCohomology` is omitted because the target does not use it. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

set_option linter.unusedVariables false in
/-- The `i = -1` half of the local class-field-axiom theorem on the actual field-unit
representation.  This is Hilbert 90 transported through the cyclic
`H¹ ≃ H⁻¹` comparison. -/
def unitsTateHminusOne_card_eq_oneStatement
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L / K), σ ∈ Subgroup.zpowers g) : Prop :=
  Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1

end

end Langlands.NYLL.LocalClassFieldTheory
