/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Sylow

/-!
# NYLL abstract reciprocity: Sylow subgroups and coprime multiples

Modified by Worker 68, 13 November 2026: extract the asserted type of M078.005, lines
144–150 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as a Prop-valued definition without its proof.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to the theorem name and use a
focused Mathlib import. See the paired Markdown for all changes and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

namespace FiniteGaloisSubextension

-- Preserve the source hypothesis and instance names even when the conclusion does not
-- mention them.
set_option linter.unusedVariables false in
/-- Target of `FiniteGaloisSubextension.sylowAddSubgroup_le_nsmul_range_of_coprime`: a Sylow
`p`-subgroup `S` of an abelian group `B` lies in the range of the additive `n`-fold map on `B`
when `n` is prime to `p`. -/
def sylowAddSubgroup_le_nsmul_range_of_coprimeStatement
    {B : Type*} [AddCommGroup B]
    {p n : ℕ} [Fact p.Prime]
    (S : Sylow p (Multiplicative B)) (hn : Nat.Coprime n p) : Prop :=
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B) n).range

end FiniteGaloisSubextension

end
end Langlands.NYLL.ClassFormation
