/-
Ported from `Theorems/Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range)
    {d : ℕ} (x : Fin d → L) (hx : AlgebraicIndependent K x) (y : L)
    (F : Polynomial (MvPolynomial (Fin d) K)) (hFm : F.Monic)
    (hFirr : Irreducible (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))))
    (hFsep : (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))).Separable)
    (hroot : F.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom y = 0) :
    Irreducible (F.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) :=
  P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.solution hsc x hx y F hFm hFirr hFsep hroot
