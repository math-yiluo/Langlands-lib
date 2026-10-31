/-
Ported from `Theorems/Thm_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map
    {R A D C : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing C] [Algebra R A] [Algebra R D] [Algebra R C]
    (φ : D →ₐ[R] C) (hφ : φ.toRingHom.FiniteType)
    (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ)) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) :=
  P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution φ hφ hA s
