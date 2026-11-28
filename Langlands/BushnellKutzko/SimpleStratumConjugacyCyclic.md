# Comparison of two cyclic splitting bases

This is an internal step in the proof of the case `t = n − 1` of BK93 (2.6.1). Source:
Bushnell–Kutzko (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`, printed
pp. 83–84 (PDF pp. 95–96). It uses the cyclic lift of the module
`CriticalDerivedCyclicBasis`, which follows the layer constructions of §2.5, printed
pp. 76–83 (PDF pp. 88–95).

## Results

- `exists_cyclicBasis_count`: the cyclic splitting basis of
  `CriticalDerived.exists_cyclicBasis`, with its number of generators on each of the
  first `g` layers recorded. That number times `deg P` is the dimension of the layer
  over `k_F`. The construction is that of `CriticalDerived.exists_cyclicBasis`. The proof
  and its two private reindexing helpers are repeated here because the original
  statement does not record the numbers of generators. The bases of the layers over
  the residual field `k_F[X]/(p)` are bases of vector spaces over that field. The tower
  law (`Module.finrank_mul_finrank`) then computes their sizes.
- `exists_unit_conj_action`: let `B₁`, `B₂` be cyclic bases for pairs `(z₁, τ₁)` and
  `(z₂, τ₂)` with the same cyclic algebra `M` and the same numbers of generators. There
  is a unit `u` of `𝔄` with `u · B₂.action x = B₁.action x · u` for every `x ∈ M`.

## Proof of `exists_unit_conj_action`

The free modules over `M` of the two bases are identified by reindexing the generators
along the equalities of their numbers (`Finsupp.domLCongr`). The unit `u` is
`B₁.transport ∘ e ∘ B₂.transport⁻¹`, which is `M`-linear on the free modules
(`CyclicBasis.action_apply`). It sends `B₂.basis t` to `B₁.basis t'`, where `t'` has
the same initial layer and the same exponents as `t`. Both vectors have exact depth
`cyclicWeight t`. The test of filtration degrees on a splitting basis
(`mem_endFiltration_iff_splittingBasis`) therefore puts `u` and `u⁻¹` in `𝔄`.
