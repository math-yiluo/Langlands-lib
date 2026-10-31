/-
Ported from `Theorems/Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f] [LocallyOfFinitePresentation f]
    [Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))] (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))) :=
  P2MW.S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.solution f s
