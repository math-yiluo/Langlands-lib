/-
Ported from `Theorems/Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.FiniteType
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_charZero
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


theorem HopfAlgebra.isReduced_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by
  exact _root_.P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero.solution K A
