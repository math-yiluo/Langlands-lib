/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified in Langlands-lib, 26 November 2026: FLT module names are prefixed by
`Langlands.AnthropicFLT`; `import Mathlib` is replaced by `import Langlands.MathlibBase`; the
FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof
`by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem AlgebraicGeometry.Scheme.exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
    {Z : Scheme.{0}} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
    (i₀ : Fin r) (g : Γ(Z, V i₀)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, Γ(Z, V j), t i₀ = g ∧
      ∀ j m : Fin r,
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) :=
  P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution V hV w hW1 hW2 hW3 i₀ g
