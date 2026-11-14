/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M141.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean,
lines 59-72, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import only the published
ValueGroupCohomology Statements module, and prove the published target
applied to all its parameters with the original proof, after unfolding the
target. Replace the source docstring, which only restates the theorem's
name, by a descriptive one. Omit the source noncomputable section and all
other source declarations. See the paired Markdown; the original LICENSE and
NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Statements

/-!
# Reduction modulo the Galois order is surjective

Reduction modulo `|Gal(L/K)|` on the fixed subgroup of the trivial
value-group module is surjective.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology
open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe u

/-- Reduction modulo the Galois order on the fixed value group is surjective. -/
theorem galoisGroupValueGroupFixedToZModHom_surjective
    (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    galoisGroupValueGroupFixedToZModHom_surjectiveStatement K L := by
  unfold galoisGroupValueGroupFixedToZModHom_surjectiveStatement
  let := galoisGroupValueGroupMulDistribMulAction K L
  intro y
  rcases ZMod.intCast_surjective (Multiplicative.toAdd y) with ⟨z, hz⟩
  let x : fixedSubgroup (Gal(L / K)) (Multiplicative Int) :=
    ⟨Multiplicative.ofAdd z, by intro σ; rfl⟩
  refine ⟨x, ?_⟩
  rw [show galoisGroupValueGroupFixedToZModHom K L x =
      Multiplicative.ofAdd
        ((z : Int) : ZMod (Fintype.card (Gal(L / K)))) by rfl]
  exact congrArg Multiplicative.ofAdd hz

end Langlands.NYLL.LocalClassFieldTheory
