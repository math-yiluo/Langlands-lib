/-
Ported from `Theorems/Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
    {R : Type u} [CommRing R] (T : Type u) [CommRing T] [Algebra R T] [Module.Flat R T]
    {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : g ∘ₗ f = 0) :
    letI : AddCommGroup ↥(LinearMap.ker (g.baseChange T)) :=
      Submodule.addCommGroup (M := T ⊗[R] N) (LinearMap.ker (g.baseChange T))
    Function.Bijective (TwoChartCech.kerBaseChangeHom g T) ∧
    Nonempty
      (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[T]
        (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) ∧
    ((LinearMap.ker (g.baseChange T) ≤ LinearMap.range (f.baseChange T)) ↔
        Subsingleton (T ⊗[R] (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype))) ∧
    (Module.Finite R (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) →
        Module.Finite T (↥(LinearMap.ker (g.baseChange T)) ⧸
          (LinearMap.range (f.baseChange T)).comap (LinearMap.ker (g.baseChange T)).subtype)) :=
  P2MW.S_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv.solution T f g hfg
