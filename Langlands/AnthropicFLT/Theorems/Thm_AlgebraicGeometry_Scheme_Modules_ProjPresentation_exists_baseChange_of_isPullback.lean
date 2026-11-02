/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X X' : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of A)} {p : X' ⟶ X}
    (sq : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f N) :
    ∃ 𝔓' : ((Scheme.Modules.pullback p).obj M).ProjPresentation f' N,
      (∀ i, 𝔓'.σ i = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) (𝔓.σ i)) ∧
      𝔓'.toProj ≫ ProjSpace.map R A N = p ≫ 𝔓.toProj ∧
      IsPullback p 𝔓'.toProj 𝔓.toProj (ProjSpace.map R A N) :=
  P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback.solution sq 𝔓
