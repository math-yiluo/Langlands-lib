# Invariant integration and sums of actual simple subrepresentations

For a finite coordinate matrix representation over any field, `IsSemisimple`
says that the supremum of its nonzero simple stable subspaces is the entire
coordinate space. Here stability is the existing `IsStableSubspace` condition,
tested over every commutative ground-field algebra.

The theorem `isSemisimple_of_stable_complements` proves this condition if every
stable subspace has a stable complement. Consequently,
`isSemisimple_of_invariantIntegral` proves semisimplicity from a normalized
all-algebra invariant coordinate integral, using the averaging theorem in
`InvariantIntegralSplitting`. No characteristic, connectedness, smoothness or
finite-type hypothesis is used in this implication; the group is assumed affine
in its invariant-integral application.

## Proof

The coefficient-vector operation associated to an affine point and a linear
functional is additive. Submodule supremum induction therefore proves that
sums of stable subspaces are stable (`IsStableSubspace.sSup`). The theorem
`exists_minimal_nonzero_stableSubspace_le` chooses a nonzero stable subspace of
minimal finite dimension inside a given nonzero stable subspace; any nonzero
stable subspace of it has at least its dimension and hence equals it.

Take a stable complement to the sum of all simple stable subspaces. If this
complement were nonzero, the minimal-dimension lemma would produce a simple
stable subspace in it. That subspace belongs to the sum, contradicting the
trivial intersection of the complement and the sum. The complement is therefore
zero and the sum is the whole space. Averaging supplies the complement property
in the final theorem.

## Provenance

This is a derived internal proof from the Library's all-affine-tests stable
subspace API, its minimum-dimension argument, and its invariant-integral
averaging construction. The definition agrees with James S. Milne, *Algebraic
Groups* (2017), Definition 4.15, printed p.90 (PDF p.106), registered source
`milne-2017-algebraic-groups`. The stable-complement criterion is discussed after
Proposition 4.17 on the same page. The proof describes the implemented socle and
minimal-dimension argument. The author errata for the 2017 edition and 2022
reprint do not change these definitions or this criterion.

The semisimplicity predicate `IsSemisimple` and stable-supremum lemma
`IsStableSubspace.sSup` are reused from `StableComplements`; the all-test
sum-of-simple-subspaces formula is unchanged.
