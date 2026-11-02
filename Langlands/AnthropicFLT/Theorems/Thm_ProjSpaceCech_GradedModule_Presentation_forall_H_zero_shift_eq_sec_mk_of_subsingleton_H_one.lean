/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
    {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (d : ℤ)
    (hK : Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.ker d) 1))
    (hF : ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.F d) 0,
      ∃ f : σ.F.M, f ∈ σ.F.grade d ∧
        ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift σ.F d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift σ.F d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift σ.F d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, f, hf⟩) :
    ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
      ∃ m : D.M, m ∈ D.grade d ∧
        ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, m, hm⟩ :=
  P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.solution σ d hK hF
