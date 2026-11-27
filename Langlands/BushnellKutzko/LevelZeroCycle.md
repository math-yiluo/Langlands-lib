# Injectivity of compression by an inverse block cycle

`cyc k` is the cycle `(0 1 … k)` of the blocks. It sends `j < k` to `j + 1`,
sends `k` to `0`, and fixes the blocks after `k`. The identity `cyc_succ`
extends `cyc k` by the transposition of blocks `k, k + 1`.

In `compressionMap_cyc_comp_eq_zero`, let `K = U^1(𝔄)` and let `ρ` be a
representation of `U(𝔄)` trivial on `K`, with the sums
`∑_Z ρ(diag(unipLift r Z, 1))` on blocks `0, m` vanishing for `m > 0` and
`0 < r < f`. If compression by the permutation matrix of `(cyc k)⁻¹`
kills a map `φ` intertwining `ρ` with a smooth representation `π`, then
`φ = 0`.

The proof inducts on `k`. A factorization of elements of `K` into lower
and upper parts gives multiplicativity of compression along the
factorization of `(cyc (k + 1))⁻¹`. Composing `φ` with compression by the
inverse of `cyc k` produces a map that intertwines the block diagonal action
on blocks `k, k + 1` with the action of `ρ` on blocks `0, k + 1`. This follows from
`permGL_conj_pairGL`. The transposition step and the induction hypothesis
then force `φ = 0`. [Transposition step](LevelZeroSwapStep.md)
