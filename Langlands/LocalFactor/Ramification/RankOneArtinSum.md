# The Artin expression of an inertia character through its upper levels

Authors: Worker 4918, with Worker 4803, whose draft supplied the profile argument
(written for Task 5815, rank-one conductor transport).

## Statements

`Ramification.Padic.finrank_fixedVectors_rankOne`: for a group `G`, a character
`ρ : G →* ℂˣ` and a subgroup `H`, the vectors of the line `ℂ` fixed by `H` under
`rankOneCharacterRepresentation ρ` have dimension `1` if `ρ` is trivial on `H` and `0`
otherwise.

`Ramification.Padic.inertiaArtinConductor_rankOne_eq_of_upper_levels`: let `T` be
topological data of a p-adic field `F` over a base field `K` (the generic setting of
module `Langlands.LocalFactor.Ramification.Galois`; no Galois hypothesis), `ρ` a character
of the inertia group `inertia T K`, and `a` a natural number. Suppose that for every real
`s ≥ 0`, `a ≤ ⌈s⌉` holds exactly when `ρ` is trivial on every inertia element lying in the
upper ramification group `upperRamificationGroup T K s`. Then the Library's inertia Artin
expression `inertiaArtinConductor T K (rankOneCharacterRepresentation ρ)` equals `a`.

## Source

This is the rank-one case of Serre, *Local Fields* (1979), VI §2, Proposition 5 and its
Corollary, printed p. 102 (PDF p. 109): the Artin conductor of a degree-one character is
`φ(c) + 1`, `c` its last lower break, and `0` for the unit character. Here the hypothesis
describes the upper break directly through the levels `⌈s⌉`; it forces the break `t` to be
an integer, which is how this lemma is used with local class field theory (Serre XV §2).

## Proof

The first lemma: if `ρ` is trivial on `H`, every vector is fixed, so the fixed space is
the whole line. Otherwise pick `h ∈ H` with `ρ(h) ≠ 1`; a fixed `z` satisfies
`(ρ(h) − 1) z = 0`, so `z = 0`.

The main theorem uses the profile formula `inertiaArtinConductor_eq_integral` of module
`Langlands.LocalFactor.Ramification.InertiaConductorProfile`: for `B` at least
`φ(ramificationCutoff)`, the real Artin expression equals `d(0) + ∫_0^B d(v) dv`, where
`d(v) = upperCodimensionProfile` is `dim V − dim V^(G^v)` for the inertia elements of the
upper group `G^v`. For the line `ℂ` the first lemma and the hypothesis give
`d(v) = 0` if `a ≤ ⌈v⌉` and `d(v) = 1` otherwise, for every `v ≥ 0`
(`Subgroup.mem_subgroupOf` matches the hypothesis with the subgroup in the profile).
Take `B = max(φ(ramificationCutoff), a)`.

- If `a = 0`, then `d` vanishes on `[0, B]`, so the expression is `0`.
- If `a = n + 1`, then `d(0) = 1`; on `[0, n]` we have `⌈v⌉ ≤ n < a`, so `d = 1` and the
  integral over `[0, n]` is `n`; on `(n, B)` we have `⌈v⌉ ≥ n + 1 = a`, so `d = 0`.
  Splitting the integral at `n` (`intervalIntegral.integral_add_adjacent_intervals`, the
  profile being antitone and hence integrable) gives `1 + n = a`.

The real equality is cast back to `ℚ`. Only the axioms `propext`, `Classical.choice` and
`Quot.sound` are used.
