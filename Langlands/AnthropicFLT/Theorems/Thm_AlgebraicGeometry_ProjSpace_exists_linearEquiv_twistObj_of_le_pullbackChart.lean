/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (m : ℕ) {i : Fin (N + 1)} {W : X.Opens} (hW : W ≤ ProjSpace.pullbackChart φ i) :
    ∃ e : ProjSpace.twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W),
      (∀ g : ProjSpace.twistObj π φ m W,
        ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ i ≤ W) (e g) = g.val i) ∧
      (∀ (a : Γ(X, W)) (j : Fin (N + 1)),
        (e.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : W ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ j)
              (ProjSpace.frameUnit φ j i) ^ m *
            ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ j ≤ W) a) :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.solution π φ m hW
