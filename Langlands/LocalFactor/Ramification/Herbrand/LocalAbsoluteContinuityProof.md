# Left continuity of absolute upper ramification

`Langlands.Ramification.Local.absoluteUpperLeftContinuity` proves
[`AbsoluteUpperLeftContinuity`](LocalAbsoluteStatement.md) for a nonarchimedean
local field `K` of either characteristic and its specified separable closure `Ω`,
in independent universes.
For each real `v > -1`, the absolute upper subgroup at `v` equals the intersection
of those at `w` with `-1 ≤ w < v`.

## Proof

At a finite level, let `n = ⌈ψ(v)⌉`, where `ψ` is the inverse Herbrand function.
The strict inequality `n - 1 < ψ(v)` persists in a left neighborhood by
`herbrandPsi_continuous`. Since `v > -1`, this neighborhood contains some
`w` with `-1 < w < v`. By `herbrandPsi_strictMono` we have `ψ(w) < ψ(v) ≤ n`.
Thus `Int.ceil_eq_iff` gives `⌈ψ(w)⌉ = n`, and
`upperRamificationGroup_eq_lower` identifies the finite upper groups at `w`
and `v`.

The absolute group at `v` lies in every group at `w < v` by antitonicity.
For the reverse inclusion, fix an element of the intersection and a finite
Galois subextension `L`. With `localTopologicalData K L`, the finite argument
gives an index `w` at which the two finite upper groups of `L/K` agree.
Membership in the absolute group at that `w` puts the restriction of the
element in the finite upper group at `v`. Applying this to every `L` proves
membership in the defining intersection of restriction preimages at `v`.
The index `w` may depend on `L`.

## Source

Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67, Springer
(1979), Chapter IV §3, pp. 73–74 for the ceiling convention and inverse
Herbrand function, and Remark 1, p. 75 for left continuity of the inverse-limit
filtration. The registered source is `serre-1979-local-fields`, with SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The finite-level argument follows the p-adic proof in
[`Herbrand.AbsoluteProof`](AbsoluteProof.md), using the general finite groups
and the canonical norm of `K`.
