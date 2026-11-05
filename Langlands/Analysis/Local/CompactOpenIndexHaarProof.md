# Haar characters from compact-open indices: proof

Authors: Worker 103 (original proof draft), Worker 1643 (verification and submission).

`Langlands.Haar.compactOpenIndexHaar` proves exactly
`Langlands.Haar.CompactOpenIndexHaarStatement.{u}` for every universe `u`,
without additional outer hypotheses. It imports the published statement
and leaves the statement and its imports unchanged.
`finiteIndex_subgroupOf_compact_open` views the coset space of the open
intersection subgroup of `K` as a compact discrete space. It is finite.

`relIndex_mul_measure` pulls a left-invariant ambient measure back along
the inclusion of the open subgroup `K`. Mathlib's `Subgroup.index_mul_measure`
then gives `[K : J] * μ(J) = μ(K)`. The containment `J ≤ K` identifies the
image of the intersection subgroup with `J`.

The main proof applies this identity to `J` and its literal image under
`α`. The regular Haar scaling identity gives
`μ(α(J)) = mulEquivHaarChar α * μ(J)`. The positive, finite mass of `J`
can be cancelled, giving the asserted index equation. Both indices are
positive, so the equation also proves the claimed equivalence with
triviality of the Haar character.

The argument is an internal consequence of Mathlib's finite-coset measure
formula and continuous-automorphism Haar scaling. It uses the canonical
regular Haar measure and no reductive-group structure. Applications still
need their actual automorphism, compact open subgroups and index
comparisons; this proof supplies no Iwahori decomposition or reductive-group
unimodularity theorem.
