/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤))
    (U : Fin (N + 1) → X.Opens) (hU : iSup U = ⊤)
    (hframe : ∀ i (V : X.Opens), V ≤ U i →
       Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧ ∀ i, U i ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) :=
  P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.solution f M N σ U hU hframe
