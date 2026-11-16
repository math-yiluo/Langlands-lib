/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: reuse published M145.003 by Lean name and check
-- its complete effective source telescope. See StableQuotient.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.QuotientDistribAction.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe uG uA

example (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) :
    MulDistribMulAction G (A ⧸ V) :=
  quotientMulDistribMulActionOfSubgroupStable G A V hstable

end

end Langlands.NYLL.LocalClassFieldTheory
