/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 168: isolated the M001.001 proof in Langlands.NYLL,
imported its published statement, and made that statement the theorem type.
-/

import Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Statements

/-!
# Continuity of automorphism conjugation in the Krull topology

Proof of the published M001.001 target, adapted from NYLL's
`AlgebraicNumberTheory.continuous_algEquiv_autCongr` (lines 28–57).
-/

namespace Langlands.NYLL.AlgebraicNumberTheory

/-- Conjugation by an algebra equivalence is continuous for the Krull topologies. -/
theorem continuous_algEquiv_autCongr
    {F E E' : Type*}
    [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') :
    continuous_algEquiv_autCongrStatement e := by
  change Continuous (AlgEquiv.autCongr e)
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hMfinite, hMs⟩ := hs
  let : FiniteDimensional F M := hMfinite
  let N : IntermediateField F E :=
    M.map e.symm.toAlgHom
  let : FiniteDimensional F N :=
    (M.equivMap e.symm.toAlgHom).toLinearEquiv.finiteDimensional
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨N, inferInstance, ?_⟩
  intro σ hσ
  apply hMs
  apply (IntermediateField.mem_fixingSubgroup_iff M
    (AlgEquiv.autCongr e σ)).2
  intro x hx
  have hxN : e.symm x ∈ N :=
    ⟨x, hx, rfl⟩
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff N σ).1 hσ
      (e.symm x) hxN
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

end Langlands.NYLL.AlgebraicNumberTheory
