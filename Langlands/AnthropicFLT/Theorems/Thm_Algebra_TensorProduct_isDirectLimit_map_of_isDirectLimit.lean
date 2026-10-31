/-
Ported from `Theorems/Thm_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open TensorProduct

universe u v w

theorem Algebra.TensorProduct.isDirectLimit_map_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (R₀ : Type v) [CommRing R₀]
    (G : ι → Type w) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (B : Type w) [CommRing B] [Algebra R₀ B] :
    ∃ _ : DirectedSystem (fun i => G i ⊗[R₀] B)
        (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B))),
      IsDirectLimit (fun i j h => ⇑(Algebra.TensorProduct.map (f i j h) (AlgHom.id R₀ B)))
        (fun i => ⇑(Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B))) := by exact @_root_.P2MW.S_Algebra_TensorProduct_isDirectLimit_map_of_isDirectLimit.solution ι _ _ _ R₀ _ G _ _ f _ R _ _ _ _ hR B _ _
