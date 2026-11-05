/-
Ported from `Theorems/Thm_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


theorem HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A]
    {ι : Type*} [Fintype ι] {ξ : ι → A}
    (hξI : ∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)
    (hξli : LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
      ∃ c : ι → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2)
    {m n : ℕ} {x y : A}
    (hxm : x ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ m)
    (hxm' : x ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + 1))
    (hyn : y ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ n)
    (hyn' : y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (n + 1)) :
    x * y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + n + 1) := by
  exact _root_.P2MW.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero.solution
    K A hξI hξli hξspan hxm hxm' hyn hyn'
