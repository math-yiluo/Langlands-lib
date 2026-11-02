/-
Ported from `Theorems/Thm_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_SmoothFieldFiberRegularStalksStandardSmoothReduction
import Langlands.AnthropicFLT.P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

theorem isRegularLocalRing_localization_atPrime_of_isStandardSmooth
    (k B : Type*) [Field k] [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.solution k B q
