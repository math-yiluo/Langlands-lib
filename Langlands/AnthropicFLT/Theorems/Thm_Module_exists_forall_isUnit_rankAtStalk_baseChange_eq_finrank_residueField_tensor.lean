/-
Ported from `Theorems/Thm_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (𝔭 : PrimeSpectrum R) (g : R) (hg : g ∉ 𝔭.asIdeal)
    (hproj : ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g) → Module.Projective A (A ⊗[R] M)) :
    ∃ g' : R, g' ∉ 𝔭.asIdeal ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') → IsUnit (algebraMap R A g)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A], IsUnit (algebraMap R A g') →
        ∀ 𝔮 : PrimeSpectrum A,
          Module.rankAtStalk (A ⊗[R] M) 𝔮 =
            Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] M) :=
  P2MW.S_Module_exists_forall_isUnit_rankAtStalk_baseChange_eq_finrank_residueField_tensor.solution M 𝔭 g hg hproj
