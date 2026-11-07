/-
Ported from `Theorems/Thm_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal
attribute [-simp] Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup

set_option autoImplicit false

theorem IsDiscreteValuationRing.exists_adjoin_singleton_eq_top_of_isSeparable_residueField
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ x : B, Algebra.adjoin A {x} = ⊤ := by exact @_root_.P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.solution A _ _ _ B _ _ _ _ _ _ _ hinj
