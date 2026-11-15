/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.U002.Proofs

/-!
# The quotient action by automorphisms for a stable subgroup

Modified by Worker 5264, 15 November 2026: port the source definition M145.003
`quotientMulDistribMulActionOfSubgroupStable` of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 with its source attribute, binders,
docstring and body. Prefix the namespace with `Langlands.NYLL`, import the
published module proving `quotientActionOfSubgroupStable` (M145.002) instead of
the four source imports, omit the source `open` commands and the universe `u`,
which this declaration does not use, and omit the other source declarations.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/


namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe uG uA

/-- Descend an action by group automorphisms to the quotient by an invariant
subgroup. -/
@[implicit_reducible]
def quotientMulDistribMulActionOfSubgroupStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G (A ⧸ V) := by
  letI : MulAction.QuotientAction G V :=
    quotientActionOfSubgroupStable G A V hstable
  exact
    { smul := (· • ·)
      one_smul := one_smul G
      mul_smul := mul_smul
      smul_mul := by
        intro g x y
        refine Quotient.inductionOn₂' x y ?_
        intro a b
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_mul g a b)
      smul_one := by
        intro g
        exact congrArg QuotientGroup.mk
          (MulDistribMulAction.smul_one g) }

end

end Langlands.NYLL.LocalClassFieldTheory
