/-
Ported from `Theorems/Thm_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Ideal.exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective
    {R A K : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field K] [Algebra R K]
    (J : Ideal A) (hJ : J.FG) [Module.Flat R (A ⧸ J)]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hK : RingHom.ker (algebraMap R K) = 𝔭.comap (algebraMap R A))
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ R J).toLinearMap.rTensor K)) :
    ∃ s : A, s ∉ 𝔭 ∧ ∀ j ∈ J, s * j = 0 :=
  P2MW.S_Ideal_exists_notMem_and_forall_mul_eq_zero_of_flat_quotient_of_rTensor_injective.solution J hJ 𝔭 hK hinj
