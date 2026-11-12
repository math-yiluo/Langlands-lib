# Block structure of standard compact elements

Module: `Langlands.Global.SiegelFiniteness.CompactBlock`. Provenance: internal.

`infinite_entry_eq_zero hm hblock a b ha hb`: let `m` be in the standard compact subgroup
`standardCompact F n` and suppose its adelic matrix vanishes in rows `≥ s`, columns `< s`
(`IsBlockUpper s`). Then for `a < s ≤ b` the archimedean component of the entry `m_{ab}`
vanishes. At every infinite place `w` the coordinate matrix of `m` (real at a real place,
complex at a complex place, `mem_standardInfiniteCompact_iff`) is orthogonal or unitary and
inherits the block condition, so its upper-right block vanishes
(`unitary_upperRight_eq_zero`); the coordinate maps preserve norms (`norm_realCoord`,
`norm_complexCoord`), so the `w`-component of `m_{ab}` is zero.
