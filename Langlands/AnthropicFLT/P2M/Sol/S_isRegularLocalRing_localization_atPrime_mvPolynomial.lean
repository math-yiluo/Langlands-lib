/-
Ported from `P2M/Sol/S_isRegularLocalRing_localization_atPrime_mvPolynomial.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_isRegularLocalRing_localization_atPrime_mvPolynomial

set_option autoImplicit false

theorem solution (k : Type*) [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := kmf2_polyasc_isRegularRing_mvPolynomial_fin k n
  exact IsRegularRing.isRegularLocalRing_localization q
