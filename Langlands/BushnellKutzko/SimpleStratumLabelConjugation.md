# Conjugating perturbations with corestriction in the next step

`Langlands.BushnellKutzko.SimpleStratumLabel.exists_unit_conj_add_sub_mem`:
let `[𝔄,n,r,β]` be a simple stratum, let `E = F[β]` act on `V` with a
generator mapping to `β`, let `s` be a tame corestriction relative to
`E/F`, and let `c, b ∈ 𝔓^{−r}` with `s(b) ∈ 𝔓^{1−r}`. Then some
`g ∈ U¹(𝔄)` satisfies

`g (β + c + b) g⁻¹ ≡ β + c (mod 𝔓^{1−r})`.

## Proof

The image of `𝔓^{1−r}` under `s` is `𝔓^{1−r} ∩ B`
(`tameCorestriction`, BK93 (1.3.4)), so some `p ∈ 𝔓^{1−r}` has
`s(p) = s(b)`. Then `b − p ∈ 𝔓^{−r}` is killed by `s`, and the adjoint
exactness of BK93 (1.4.10), in the form
`PureApproximation.exists_adjoint_eq_of_corestriction_eq_zero`, writes
`b − p = βy − yβ` with `y ∈ 𝔓¹`. With `g = 1 + y`,

`g(β + c + b) − (β + c)g = p + (yc − cy) + yb`,

and each term lies in `𝔓^{1−r}`. Multiplying on the right by
`g⁻¹ ∈ 𝔄` gives the congruence.

This is the computation of `PureApproximation.exists_conj_sub_mem` (the
conjugation step of BK93 (2.4.5), printed p. 68) with the additional
summand `c`. Source: Bushnell–Kutzko 1993,
`bushnell-kutzko-1993-admissible-dual-gln`, (1.3.4) and (1.4.10),
printed pp. 29 and 38.
