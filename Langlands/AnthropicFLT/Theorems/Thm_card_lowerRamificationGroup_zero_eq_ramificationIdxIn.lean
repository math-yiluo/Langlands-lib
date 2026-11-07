/-
Ported from `Theorems/Thm_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_DifferentFiltrationFormula
import Mathlib.NumberTheory.RamificationInertia.Galois
import Langlands.AnthropicFLT.P2M.Sol.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem card_lowerRamificationGroup_zero_eq_ramificationIdxIn
    {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [MulSemiringAction G B]
    [IsDedekindDomain A] [Module.Finite A B] [IsGaloisGroup G A B] [Finite G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Nat.card (IsLocalRing.lowerRamificationGroup B G 0)
      = (IsLocalRing.maximalIdeal A).ramificationIdxIn B := by exact @_root_.P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn.solution A _ _ B _ _ _ _ _ G _ _ _ _ _ _ _ _ hp
