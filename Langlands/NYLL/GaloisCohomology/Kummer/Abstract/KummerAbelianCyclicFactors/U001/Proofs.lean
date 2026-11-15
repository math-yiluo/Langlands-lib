/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 15 November 2026 UTC:
Extract only the proof of M020.001
(finiteCommGroup_exists_jointlyFaithful_cyclic_factors) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean
(lines 33–59) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix and import only the published
KummerAbelianCyclicFactors Statements module. Keep the section name, the
noncomputable section, the docstring, the binders and the tactic proof, state
the theorem as the published Statement applied to the source parameter, and
add a leading `unfold` of that Statement. Omit the source's
`open CyclicCohomology`, which this proof does not use, and the other
declarations of the source file. The original LICENSE and NOTICE are retained
in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements

/-!
# Jointly faithful cyclic factors of a finite abelian group

By the structure theorem, a finite commutative group `Q` is isomorphic to a
finite product of cyclic groups `Multiplicative (ZMod (m i))` with
`1 < m i`. The coordinate maps of such an isomorphism are surjective and
their kernels meet trivially.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

section FiniteAbelianCyclicFactors

/-- Coordinate characters obtained from the structure theorem separate the
elements of a finite commutative group. -/
theorem finiteCommGroup_exists_jointlyFaithful_cyclic_factors
    (Q : Type*) [CommGroup Q] [Finite Q] :
    finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement Q := by
  unfold finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let f : ∀ i, Q →* Multiplicative (ZMod (m i)) := fun i =>
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e
  refine ⟨ι, hι, m, hm, f, ?_, ?_⟩
  · intro i
    exact (Function.surjective_eval i).comp e.surjective
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply e.injective
      ext i
      have hxi : x ∈ MonoidHom.ker (f i) :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

end FiniteAbelianCyclicFactors

end

end Langlands.NYLL.KummerTheory
