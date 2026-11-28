# Centralizer products of H lattices

For a simple stratum with lower index zero and a chosen defining sequence,
`SplitBlocks.mul_mem_simpleHLayer_of_mem_centralizer` proves that `𝔥ᵏ` is stable
under both actions of the integral centralizer order `𝔅`.
The proof uses the ring and ideal properties of the H lattices in
Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups* (1993),
(3.1.9)(iii)–(iv), printed p. 91.

`SplitBlocks.mul_mul_mem_simpleHLayer_of_inv` proves that a product of two
elements of `𝔥ᵐ`, `m ≥ 1`, and one element of `𝔔⁻¹` belongs to `𝔥ᵐ` in each
of the three orders of the factors. The proof applies the square bound
(8.2.13), commutes fractional centralizer powers with the H layer using
(3.1.11), printed p. 94, and uses `𝔔⁻¹ 𝔔 ⊆ 𝔅` and `𝔔 𝔔⁻¹ ⊆ 𝔅`.
