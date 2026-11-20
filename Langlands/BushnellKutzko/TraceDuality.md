# Trace duality for the filtration of a lattice chain

Lean proof by Worker 408 for Task 7683.

## Statement

`Langlands.BushnellKutzko.LatticeChain.mem_endFiltration_one_sub_of_forall`. Let `F` be a
nonarchimedean local field, `ι` a finite type, and `𝓛` a lattice chain in `F^ι`. Let `ψ : AddChar F ℂ`
satisfy `ψ(a) ≠ 1` for some `a ∈ 𝔬_F`, and let `k ∈ ℤ`. If `ψ(tr(y z)) = 1` for every
`z ∈ 𝔓^k(𝓛)`, then `y ∈ 𝔓^{1-k}(𝓛)`.

This is the inclusion `(𝔓^k)^* ⊆ 𝔓^{1-k}` from the annihilator formula following
Bushnell–Kutzko (1993), (1.1.4), printed p. 22. The inclusion uses just the
nontriviality of `ψ` on `𝔬_F`.

## Proof

Choose a uniformizer `ϖ` and a basis `β` splitting `𝓛` (`exists_basis_splits_both`). Write
`y = ∑ E_{kl}(y_{kl})` (`sum_elementaryEnd_entry`). It suffices that every term with `y_{kl} ≠ 0`
lies in `𝔓^{1-k}(𝓛)`. By `elementaryEnd_mem_iff`, that membership is the inequality
`(1 - k) + ν(β_l) ≤ e(𝓛) ord(y_{kl}) + ν(β_k)`. Suppose it fails. Put `t = a y_{kl}^{-1}`. Since
`ord(a) ≥ 0`, the same criterion shows `E_{lk}(t) ∈ 𝔓^k(𝓛)`. By `trace_mul_elementaryEnd`,
`tr(y E_{lk}(t)) = t y_{kl} = a`, so the hypothesis gives `ψ(a) = 1`, a contradiction.
