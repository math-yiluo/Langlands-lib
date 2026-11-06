/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    {π : X ⟶ Spec (CommRingCat.of A)} (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ (m : ℕ) (s : Fin m → ∀ i : Fin (N + 1), F.obj (ProjSpace.pullbackChart φ i)),
        (∀ (a : Fin m) (i j : Fin (N + 1)),
          F.res (ProjSpace.pullbackOverlap_le_left φ i j) (s a i) =
            ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j) ^ d •
              F.res (ProjSpace.pullbackOverlap_le_right φ i j) (s a j)) ∧
        ∀ i : Fin (N + 1),
          Submodule.span Γ(X, ProjSpace.pullbackChart φ i) (Set.range fun a : Fin m => s a i) = ⊤ :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.solution φ F hc hq
