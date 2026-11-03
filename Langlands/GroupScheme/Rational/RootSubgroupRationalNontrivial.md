# Nonidentity rational points in every actual root subgroup

This internal derived unit proves nonidentity rational point existence for
every actual relative root of a smooth affine group over an arbitrary field,
acted on by a split torus through the given homomorphism. It uses the existing
actual orbit-extension subgroup functor. Connected reductivity, maximal
splitness, and a relative-root system are not hypotheses.

The natural multiples of a nonzero split-torus character are distinct: pair
with a cocharacter having positive pairing and cancel that positive integer.
The finite ambient Lie weight support therefore gives finitely many natural
multipliers that are actual roots. A maximal one is positive, and its character
has no second or higher positive multiple that is a root.

For a character with no higher positive roots, the published cyclic
comparison identifies the first cyclic weight subgroup with the actual root
functor. The higher-root vanishing lemma makes its second term trivial.
The published cyclic filtration gives a vector group quotient by that second
term. An fppf quotient with trivial actual kernel is an isomorphism, so every
representative of this root functor is a vector group.

For an actual root the first weight space is nonzero and lies in the positive
cyclic Lie span. The exact Lie image theorem and the existing vector group
point lemma then give a nonidentity rational point of the maximal-multiple
root subgroup. The unconditional inclusion of each positive-multiple
orbit-extension subgroup into the original subgroup gives the point in the
original root subgroup. This argument uses actual vector coordinates and does
not assume that rational points lift along an arbitrary quotient.

`RootSubgroupRationalNontrivialStatement` packages this full arbitrary-universe
result, and `rootSubgroupRationalNontrivial` proves it. The provenance is the
internal composition of the cited imported Library proofs. This unit does not
construct opposite factor pairs or prove the rank-one factorization theorem.
