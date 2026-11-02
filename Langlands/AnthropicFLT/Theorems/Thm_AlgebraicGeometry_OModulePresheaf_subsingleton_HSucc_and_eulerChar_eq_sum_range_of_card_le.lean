/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.solution F K
