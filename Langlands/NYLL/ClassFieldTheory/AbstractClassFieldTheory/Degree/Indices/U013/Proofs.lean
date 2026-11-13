/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 173, 13 November 2026:
Extract the proof of M006.013 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL, give the theorem the published statement
relativeIndexCardinal_selfStatement K as its type, and import only the
U012 Statements module. The proof steps are kept unchanged; the
theorem-only simp attribute and the unused section variables D and
Group D are omitted. The upstream LICENSE and NOTICE are preserved in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements

/-!
# The cardinal index of a subgroup in itself

The actual coset type of a subgroup modulo itself has exactly one element,
so its cardinal relative index is one.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G]

/-- Establishes the identity `relativeIndexCardinal (le_refl K) = 1`. -/
theorem relativeIndexCardinal_self (K : Subgroup G) :
    relativeIndexCardinal_selfStatement K := by
  let α := K ⧸ K.subgroupOf K
  let : Subsingleton α := by
    constructor
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    apply Quotient.eq''.mpr
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    exact (x⁻¹ * y).2
  change Cardinal.mk α = 1
  exact Cardinal.mk_eq_one α

end Langlands.NYLL.ClassFormation
