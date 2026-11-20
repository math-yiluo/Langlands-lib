import Langlands.BushnellKutzko.FundamentalStratumDual

/-! # Trace duality for the filtration of a lattice chain

Bushnell–Kutzko (1993), (1.1.4), printed p. 22: for an additive character `ψ` of `F`
that is nontrivial on `𝔬_F`, every `y` with `ψ(tr(y z)) = 1` for all `z ∈ 𝔓^k(𝓛)` lies in
`𝔓^{1-k}(𝓛)` (`LatticeChain.mem_endFiltration_one_sub_of_forall`). This is the inclusion
`(𝔓^k)^* ⊆ 𝔓^{1-k}` of the duality `(𝔓^k)^* = 𝔓^{1-k}` for a character trivial on `𝔭_F` (the
reverse inclusion is not needed here).

Proof. Write `y = ∑ E_{kl}(y_{kl})` in a basis splitting `𝓛`. If some `E_{kl}(y_{kl})` with
`y_{kl} ≠ 0` is not in `𝔓^{1-k}(𝓛)`, then `z = E_{lk}(a y_{kl}^{-1})` lies in `𝔓^k(𝓛)` for every
`a ∈ 𝔬_F`, and `tr(y z) = a`. Taking `a` with `ψ(a) ≠ 1` gives a contradiction.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe u

section TraceDuality

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι]

namespace LatticeChain

/-- **Trace duality** (BK93 (1.1.4), printed p. 22, one inclusion). Let `ψ` be an
additive character of `F` with `ψ(a) ≠ 1` for some `a ∈ 𝔬_F`. If `ψ(tr(y z)) = 1` for all
`z ∈ 𝔓^k(𝓛)`, then `y ∈ 𝔓^{1-k}(𝓛)`. -/
theorem mem_endFiltration_one_sub_of_forall (𝓛 : LatticeChain 𝒪[F] F (ι → F))
    (ψ : AddChar F ℂ) (hψ' : ∃ a : 𝒪[F], ψ (a : F) ≠ 1) {k : ℤ}
    {y : Module.End F (ι → F)}
    (h : ∀ z ∈ 𝓛.endFiltration k, ψ (LinearMap.trace F (ι → F) (y * z)) = 1) :
    y ∈ 𝓛.endFiltration (1 - k) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := hψ'
  have ha0 : (a : F) ≠ 0 := by
    intro h0
    rw [h0, AddChar.map_zero_eq_one] at ha
    exact ha rfl
  have hord_a : 0 ≤ ordOf hϖ (a : F) := ordOf_nonneg hϖ ha0 a.2
  obtain ⟨r, β, hβ, -⟩ := exists_basis_splits_both hϖ 𝓛 𝓛
  rw [← sum_elementaryEnd_entry β y]
  refine Submodule.sum_mem _ fun k' _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hkl : entry β y k' l = 0
  · rw [hkl, elementaryEnd_zero]
    exact zero_mem _
  rw [𝓛.elementaryEnd_mem_iff hϖ hβ k' l hkl]
  by_contra hlt
  rw [not_le] at hlt
  set t : F := (a : F) * (entry β y k' l)⁻¹ with ht
  have ht0 : t ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hkl)
  have hz : elementaryEnd β l k' t ∈ 𝓛.endFiltration k := by
    rw [𝓛.elementaryEnd_mem_iff hϖ hβ l k' ht0, ht, ordOf_mul hϖ ha0 (inv_ne_zero hkl),
      ordOf_inv hϖ hkl]
    have he : (0 : ℤ) < 𝓛.period := by exact_mod_cast 𝓛.period_pos
    nlinarith
  have htr := h _ hz
  rw [trace_mul_elementaryEnd, ht, mul_assoc, inv_mul_cancel₀ hkl, mul_one] at htr
  exact ha htr

end LatticeChain

end TraceDuality

end Langlands.BushnellKutzko
