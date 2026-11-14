/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness and cardinality transport along `ModuleCat ℤ` isomorphisms

Modified by Worker 5454: extract the asserted types of M117.018
`finite_source_of_moduleIso`, M117.019 `finite_target_of_moduleIso` and
M117.020 `moduleCat_card_eq_of_iso` from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`
(lines 341–363) as Prop-valued definitions. Prefix the namespace with
`Langlands.NYLL` and append `Statement` to each theorem name. The section
variables of lines 28–35 are mentioned by none of the three theorems, so
none is included; each target keeps exactly the theorem's own parameters in
order and binder kind. Proofs are omitted. The source imports are replaced by
the two Mathlib modules that state the targets. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

open CategoryTheory

set_option linter.unusedVariables false in
/-- Finiteness transports from the target to the source of a
`ModuleCat ℤ` isomorphism. -/
def finite_source_of_moduleIsoStatement
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite Y] : Prop :=
  Finite X

set_option linter.unusedVariables false in
/-- Finiteness transports from the source to the target of a
`ModuleCat ℤ` isomorphism. -/
def finite_target_of_moduleIsoStatement
    {X Y : ModuleCat.{0} ℤ} (e : X ≅ Y) [Finite X] : Prop :=
  Finite Y

set_option linter.unusedVariables false in
/-- A `ModuleCat ℤ` isomorphism with the additive form of a commutative
group identifies their cardinalities. -/
def moduleCat_card_eq_of_isoStatement
    {X : ModuleCat.{0} ℤ} {T : Type} [CommGroup T]
    (e : X ≅ ModuleCat.of ℤ (Additive T)) : Prop :=
  Nat.card X = Nat.card T

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
