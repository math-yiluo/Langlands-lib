/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M152.001 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued target,
-- prefix the namespace and reduce imports. See SpanStatement.md.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

/-- The source target identifying the two normal-basis spans. -/
def span_normalBasis_eq_chosenNormalBasisIntegerLatticeStatement
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  Submodule.span 𝒪[K] (Set.range (IsGalois.normalBasis K L)) =
    chosenNormalBasisIntegerLattice K L

end

end Langlands.NYLL.LocalClassFieldTheory
