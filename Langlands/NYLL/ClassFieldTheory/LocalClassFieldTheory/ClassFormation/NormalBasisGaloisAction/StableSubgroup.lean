/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.GroupAction.Quotient

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Restrict an action to an invariant subgroup
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe uG uA

@[implicit_reducible]
def subgroupMulDistribMulActionOfStable
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G V where
  smul g a := ⟨g • (a : A), hstable g a a.2⟩
  one_smul := by
    intro a
    apply Subtype.ext
    exact one_smul G (a : A)
  mul_smul := by
    intro g h a
    apply Subtype.ext
    exact mul_smul g h (a : A)
  smul_mul := by
    intro g a b
    apply Subtype.ext
    exact MulDistribMulAction.smul_mul g (a : A) (b : A)
  smul_one := by
    intro g
    apply Subtype.ext
    exact MulDistribMulAction.smul_one g

end

end Langlands.NYLL.LocalClassFieldTheory
