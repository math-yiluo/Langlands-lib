# Principal congruence entries and positive-level cofinality: proof

Author: Worker 267.

This pair proves the published proposition
`Langlands.Conductor.PrincipalCongruenceBasisStatement.{u}` from
`Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement`,
keeping the arbitrary field universe `u`. The closing theorem is

- `principalCongruenceBasis : PrincipalCongruenceBasisStatement.{u}`,

the pair of the two component theorems

- `principalCongruenceEntry : PrincipalCongruenceEntryStatement.{u}`;
- `principalLevelCofinal : PrincipalLevelCofinalStatement.{u}`.

Each component is a direct application of a reusable theorem with
explicit arguments, described below. The proof uses only the existing
`principalCongruenceSubgroup`, `principalLevelSubgroup`, and
`principalLevelOpenSubgroup` constructions and adds no hypotheses. Its
only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Two-sided entry criterion

`mem_principalCongruenceSubgroup_iff O n I g` is exactly the body of
`PrincipalCongruenceEntryStatement` for a field `k`, a subring `O`, an
ideal `I : Ideal O` (including `I = ⊤`), and `g` in `GL_(n+1)(k)`.
Two small helper lemmas are proved first. `subring_coe_one_apply` says
that the identity matrix over `O` has the identity entries of `k` after
inclusion, by cases on `i = j`. `one_apply_mem_subring` concludes that
these identity entries lie in `O`.

Forward direction. Membership in the image gives an integral `h` in
`integralPrincipalCongruence n I` whose inclusion is `g`. The existing
`mem_integralPrincipalCongruence` puts `h i j - δ i j` in `I`. Its image
in `k` is `g i j - δ i j`, by `GeneralLinearGroup.map_apply`, the
subtraction coercion, and `subring_coe_one_apply`. The group inverse `h⁻¹`
lies in the same kernel subgroup, and the inclusion maps `h⁻¹` to `g⁻¹`
(`map_inv`). The same argument gives the inverse witnesses.

Reverse direction. Each witness equation `x = g i j - δ i j` writes
`g i j` as `x + δ i j`, which lies in `O`; the same holds for the entries
of `g⁻¹`. The existing `mem_integralSubgroup` then makes `g` the
inclusion of some `h` in `GL_(n+1)(O)`. Both conditions are used here:
integrality of the inverse is what makes `g` an integral group element,
so the argument is valid at `I = ⊤`. Next, the image of
`h i j - δ i j` in `k` equals the witness `x`'s image. Injectivity of the
inclusion `O → k` makes `x` equal to `h i j - δ i j`, so this difference
lies in `I`. Then `mem_integralPrincipalCongruence` puts `h` in the
reduction kernel, and `map_mem_principalCongruenceSubgroup` gives the
membership of `g`.

## Cofinality of positive levels

Fix the supplied `Field`, `ValuativeRel`, `TopologicalSpace`, and
`IsNonarchimedeanLocalField` instances on `k`. Write `𝔪` for the maximal
ideal of the supplied valuation's integer ring `O`.

`coe_principalLevelOpenSubgroup` records, by `rfl`, that the open subgroup
has the principal level subgroup as its underlying set.

`eq_one_of_forall_mem_principalLevelSubgroup` shows that an element of
every positive level `principalLevelSubgroup k n (a + 1)` is the identity.
Level `1` gives an integral representative `h`. Since the inclusion of
integral matrices is injective, `map_mem_principalCongruenceSubgroup` puts
the same `h` in every kernel modulo `𝔪^(a+1)`. Level zero is the unit
ideal, so each `h i j - δ i j` lies in `⨅ a, 𝔪^a`. Mathlib provides
`IsDiscreteValuationRing` for this integer ring, which makes it a
Noetherian local ring. Krull's intersection theorem
`Ideal.iInf_pow_eq_bot_of_isLocalRing` makes this intersection zero, so
`h = 1` and its inclusion is `1`.

`exists_pos_principalLevelOpenSubgroup_subset k n hU` proves the body of
`PrincipalLevelCofinalStatement` for an identity neighborhood `U`. The
neighborhood contains an open `W` with `1 ∈ W`. If no positive level were
contained in `U`, then the sets
`P a = principalLevelOpenSubgroup k n (a + 1) ∩ Wᶜ` would all be
nonempty. They decrease by `principalLevelSubgroup_antitone`. Each is
closed, because open subgroups of the topological group `GL_(n+1)(k)` are
closed (`OpenSubgroup.isClosed`) and `Wᶜ` is closed. `P 0` is compact by
the existing `isCompact_principalLevelOpenSubgroup` at level `1`. Cantor's
intersection theorem
`IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed`
then gives an element of every positive level outside `W`. The previous
lemma shows that this element is `1`, which lies in `W`, a contradiction.
Hence some `a + 1 > 0` has its level inside `U`.

The argument uses only the supplied topology, through the neighborhood
filter, openness, and existing compactness. It computes no explicit
neighborhood basis and chooses no other field realization. It covers every
`n`, so rank one (`n = 0`) is included. Rank zero lies outside the target.

## Provenance

The target pair cites Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III (revision April 29, 2019),
section 4, Lemma III.4.1, as motivation. The proof here is an independent
derivation and does not follow a route from that source: the entry
criterion is elementary algebra on the existing construction, and
cofinality uses compactness together with Krull's intersection theorem.
