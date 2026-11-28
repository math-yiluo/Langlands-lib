# Units of a hereditary order under conjugation; pure cosets

This module supplies the case of equal orders and levels of BK93 (2.6.2), and the
facts about pure elements used in the proof of BK93 (2.6.1).

Source: C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), registered as `bushnell-kutzko-1993-admissible-dual-gln`, (2.6.2),
printed p. 86 (PDF p. 98), and (2.3.2), printed p. 57 (PDF p. 69).

Throughout, `𝓛` is an `𝔬_F`-lattice chain over a nonarchimedean local field `F`,
`𝔄` its order and `𝔓^k = 𝓛.endFiltration k`. `Shifts 𝓛 d g` (from
`CriticalDerivedSymbols`) says that `g ∈ 𝔓^d` and `g⁻¹ ∈ 𝔓^{−d}`; for `d = 0` this means
that `g` is a unit of `𝔄`.

## Results

- `conj_not_mem_one`: if `W` is a unit of `𝔄`, then `g⁻¹ W g ∉ 𝔓` for every
  `g ∈ GL_F(V)`.
- `shifts_of_mem_normalizing`, `mem_one_or_shifts_zero`: let `R ⊆ End_F(V)` be a
  subalgebra whose nonzero elements are units normalizing the chain
  (`NormalizingUnits`). A nonzero element of `R` shifts the chain by its valuation. An
  element of `R ∩ 𝔄` lies in `𝔓` or is a unit of `𝔄`.
- `exists_shifts_of_isPure`: the element `β` of a pure stratum `[𝔄,n,r,β]` is a unit
  shifting the chain by `−n`, and every nonzero element of `F[β]` is a unit normalizing
  the chain.
- `conj_not_mem_of_shifts`: if `B` shifts the chain by `−n` and `y ∈ B + 𝔓^{1−n}`, then
  `g⁻¹ y g ∉ 𝔓^{1−n}` for every `g`.
- `conj_not_mem_of_isPure`: for a pure stratum `[𝔄,n,r,β]` and `y ∈ β + 𝔓^{1−n}`,
  `g⁻¹ y g ∉ 𝔓^{1−n}` for every `g`. This is the case of equal orders and levels of
  BK93 (2.6.2). There the stratum `[𝔄,n,n−1,β]` is fundamental by (2.3.2).

## Proofs

For `conj_not_mem_one`, suppose `X = g⁻¹Wg ∈ 𝔓`. Choose `t, t'` with `ϖ^t g` and
`ϖ^{t'} g⁻¹` in `𝔄` (`exists_uniformizer_pow_mem_endFiltration`). For every `k`,
`ϖ^{t+t'} = X^k · (ϖ^{t'} g⁻¹) W^{−k} (ϖ^t g)` lies in `𝔓^k`. Take `k = (t+t')e + 1`,
where `e` is the period. The period relation (`uniformizer_pow_end_mem_iff`) then puts
`1` in `𝔓`, which contradicts `L_1 ⊊ L_0`.

For the trichotomy, a nonzero element of `R` is a unit shifting the chain by some `s`,
and `valuation_eq_shift` identifies `s` with its valuation. If it lies in `𝔄`, then
`L_s ⊆ L_0`, so `s ≥ 0`. If `s ≥ 1` it lies in `𝔓`. If `s = 0` it is a unit of `𝔄`.

For `conj_not_mem_of_shifts`, `y ≡ B` in degree `−n`, so `y` is a unit `Y` with the same
shift (`exists_unit_of_symbolEq_self`). With `π` a uniformizer, `W = Y^e π^n` is a unit of
`𝔄`. Since `π` is central, `g⁻¹ W g = (g⁻¹ Y g)^e π^n`. If `g⁻¹ y g ∈ 𝔓^{1−n}`, this lies
in `𝔓^{e(1−n)+ne} = 𝔓^e ⊆ 𝔓`, which contradicts `conj_not_mem_one`. BK93 (2.6.2)
argues instead that the coset contains a nilpotent element, referring to [Bu1] (2.9).
The Lean proof does not use that argument.
