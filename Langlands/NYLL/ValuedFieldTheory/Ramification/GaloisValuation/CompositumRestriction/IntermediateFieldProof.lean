/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 224, 14 November 2026, using Worker 305's checked equalizer
proof, from ClassFieldTheory commit fbd320cd8b1b06487c58227e92eb135794267709,
Nyll/ValuedFieldTheory/Ramification/GaloisValuation/CompositumRestriction.lean,
M331.002 (lines 56–147). Prefix the namespace with Langlands.NYLL and prove
the exact published closed statement in independent universes u, w.
Replace the M331.001 call by Mathlib's RingHom.eqLocusField; retain the
restricted-field supremum calculation and use the published M259.002
evaluation formula in a shared local inclusion argument. Import the published
target and restriction proof; isolate M331.002 and omit unused source scaffolding.
Full modifications and source correspondence are in IntermediateFieldProof.md.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.CompositumRestriction.Statements
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Proofs

/-!
# Joint restriction from an intermediate compositum

Proof of the published M331.002 target by the intermediate field on which two
automorphisms agree.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory

universe u w

/-- If two normal intermediate fields generate a third intermediate field in
a common ambient extension, restriction from the generated field to the two
factors is jointly injective. -/
theorem intermediateFieldRestrictNormalHom_prod_injective_of_sup_eq :
    intermediateFieldRestrictNormalHom_prod_injective_of_sup_eqStatement.{u, w} := by
  intro K _ Ω _ _ E₁ E₂ F hE₁ hE₂ _ _ hsup σ τ hστ
  let Q : IntermediateField K F :=
    { RingHom.eqLocusField σ.toRingHom τ.toRingHom with
      algebraMap_mem' := fun x => by
        change σ (algebraMap K F x) = τ (algebraMap K F x)
        rw [AlgEquiv.commutes, AlgEquiv.commutes] }
  have hQ (E : IntermediateField K Ω) (hEF : E ≤ F) [Normal K E]
      (hres : intermediateFieldRestrictNormalHom E F hEF σ =
        intermediateFieldRestrictNormalHom E F hEF τ) :
      IntermediateField.restrict hEF ≤ Q := by
    intro x hx
    let y : E := ⟨(x : F).1, (IntermediateField.mem_restrict hEF x).mp hx⟩
    have hy : IntermediateField.inclusion hEF y = x := by
      apply Subtype.ext
      rfl
    have h := congrArg (fun a : E ≃ₐ[K] E => E.val (a y)) hres
    rw [intermediateFieldRestrictNormalHom_apply_val,
      intermediateFieldRestrictNormalHom_apply_val, hy] at h
    exact F.val.injective h
  have hsupF :
      IntermediateField.restrict hE₁ ⊔ IntermediateField.restrict hE₂ = ⊤ := by
    apply IntermediateField.lift_injective F
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top, hsup]
  have htop : (⊤ : IntermediateField K F) ≤ Q := by
    rw [← hsupF]
    exact sup_le (hQ E₁ hE₁ (congrArg Prod.fst hστ))
      (hQ E₂ hE₂ (congrArg Prod.snd hστ))
  apply AlgEquiv.ext
  intro x
  exact htop IntermediateField.mem_top

end Langlands.NYLL.LocalClassFieldTheory
