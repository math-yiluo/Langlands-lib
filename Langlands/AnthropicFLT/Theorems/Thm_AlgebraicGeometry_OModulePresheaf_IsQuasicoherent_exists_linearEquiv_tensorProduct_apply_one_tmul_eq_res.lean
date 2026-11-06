/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
    {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} (G : OModulePresheaf π)
    (hG : G.IsQuasicoherent) (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∃ β : Γ(X, V.1) ⊗[Γ(X, U.1)] G.obj U.1 ≃ₗ[Γ(X, V.1)] G.obj V.1,
      ∀ x : G.obj U.1, β (1 ⊗ₜ x) = G.res h x :=
  P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.solution G hG U V h
