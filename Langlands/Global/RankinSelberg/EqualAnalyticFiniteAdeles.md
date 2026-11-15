# Small integral multiples and uniform local constancy on the finite adeles

Module `Langlands.Global.RankinSelberg.EqualAnalyticFiniteAdeles`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

Topological facts about `𝔸_f` used for the finite parts of Schwartz–Bruhat functions.
`Ô = integralFiniteAdeles F` is the compact open subring `∏_v 𝒪_v`.

## Provenance

Internal; elementary consequences of the compactness of `Ô` (Library
`isCompact_integralFiniteAdeles`) and of `exists_integer_mul_mem_adicCompletionIntegers`.

## Declarations

- `exists_nat_mem_of_mem_nhds_zero`: every neighbourhood of `0` in `𝔸_f` contains a positive
  integer. The integers `1, 2, …` lie in the compact `Ô`. Cover `Ô` by finitely many translates
  of a small neighbourhood `V` with `V - V ⊆ U`. By pigeonhole two integers `k < l` lie in the
  same translate, so `l - k ∈ U`.
- `exists_nat_mul_mem_of_mem_nhds_zero`: every neighbourhood `W` of `0` contains `N Ô` for some
  `N > 0`. The tube lemma gives a neighbourhood `u` of `0` with `u · Ô ⊆ W`; take `N ∈ u`.
- `algebraMap_ringOfIntegers_mem`: `𝒪 ⊆ Ô`.
- `exists_integer_mul_mem_of_isCompact`: a compact subset of `𝔸_f` lies in `d⁻¹ Ô` for some
  nonzero `d ∈ 𝒪`. It is covered by the open sets `{a | d_a a ∈ Ô}`; take the product of the
  finitely many `d_a`.
- `exists_nat_invariant_of_isLocallyConstant`: a locally constant compactly supported function
  on `𝔸_f^n` is invariant under translation by `(N Ô)^n` for some `N > 0`. Compactness of the
  support gives a uniform neighbourhood of invariance, and the previous lemma puts `N Ô` inside
  it.
