/-
Ported from `Theorems/Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


theorem HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) := by
  exact _root_.P2MW.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.solution K A
