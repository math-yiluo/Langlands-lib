/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements

/-!
# NYLL M076.009: intermediateSubgroup_eq_iUnion_cosets

Modified by Worker 751: extract the source theorem at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, drop the unused `open KummerTheory`, and prove its published
named target using the focused statement import. The two membership lemmas
the source proof cites are replaced by the definitional unfoldings they
package. The paired Markdown records the implemented proof and every
adaptation. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- The inverse image of `S` is literally the finite union of the `G_L`
cosets indexed by the elements of `S`. -/
theorem intermediateSubgroup_eq_iUnion_cosets {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    intermediateSubgroup_eq_iUnion_cosetsStatement L S := by
  unfold intermediateSubgroup_eq_iUnion_cosetsStatement
  ext x
  constructor
  · intro hx
    -- `x ∈ L.intermediateSubgroup S` unfolds to `L.extensionQuotientMk x ∈ S`.
    have hxS : L.extensionQuotientMk x ∈ S := hx
    -- `x` lies in the coset indexed by its own quotient class.
    have hxq : x ∈ L.intermediateCoset (L.extensionQuotientMk x) := rfl
    exact Set.mem_iUnion₂.mpr ⟨L.extensionQuotientMk x, hxS, hxq⟩
  · intro hx
    obtain ⟨q, hqS, hxq⟩ := Set.mem_iUnion₂.mp hx
    -- `x ∈ L.intermediateCoset q` unfolds to `L.extensionQuotientMk x = q`.
    have hxq' : L.extensionQuotientMk x = q := hxq
    show L.extensionQuotientMk x ∈ S
    rw [hxq']
    exact hqS

end FiniteGaloisSubextension
end Langlands.NYLL.ClassFormation
