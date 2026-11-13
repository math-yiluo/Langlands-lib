/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 60, 13 November 2026 UTC:
Extract only the proof of M078.005 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Sylow.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 144–163). Add the
Langlands.NYLL namespace prefix and import only the published CoprimeNsmul
Statements module. State the theorem as the published Statement applied to
the source parameters, and insert a `show` step exposing the subgroup
inclusion before the original proof, which is otherwise unchanged. Omit the
source imports, opens, noncomputable section, section variables and all
other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Sylow.CoprimeNsmul.Statements

/-!
# Sylow subgroups of an abelian group lie in coprime multiples

A Sylow `p`-subgroup of a possibly infinite abelian group `B` lies in the range
of the additive `n`-fold map on `B` whenever `n` is prime to `p`.
-/

namespace Langlands.NYLL.ClassFormation

namespace FiniteGaloisSubextension

/-- Let `S` be a Sylow `p`-subgroup of an abelian group `B`.  If
`n` is prime to `p`, then `S` lies in the range of the additive `n`-fold
map on `B`.

The proof follows the sentence literally: `S` has `p`-power
order, so the `n`-fold map is a bijection on `S`; a preimage in `S` is in
particular a preimage in `B`. -/
theorem sylowAddSubgroup_le_nsmul_range_of_coprime
    {B : Type*} [AddCommGroup B]
    {p n : ℕ} [Fact p.Prime]
    (S : Sylow p (Multiplicative B)) (hn : Nat.Coprime n p) :
    sylowAddSubgroup_le_nsmul_range_of_coprimeStatement S hn := by
  show Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B) n).range
  intro x hx
  let xS : S := ⟨Multiplicative.ofAdd x, hx⟩
  let e : S ≃ S := S.isPGroup'.powEquiv hn.symm
  let yS : S := e.symm xS
  refine ⟨yS.1.toAdd, ?_⟩
  have hy : yS ^ n = xS := e.apply_symm_apply xS
  have hyval : yS.1 ^ n = xS.1 := congrArg Subtype.val hy
  simpa [xS] using congrArg Multiplicative.toAdd hyval

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
