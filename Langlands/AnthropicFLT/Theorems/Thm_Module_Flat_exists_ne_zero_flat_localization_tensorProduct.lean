/-
Ported from `Theorems/Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct in

theorem Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) :=
  P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.solution
