# Actual root rays from opposite factor pairs

Worker 1314, using Worker 1536's integral-coroot argument. This internal
derived unit proves ray disjointness from `HasOppositeFactorPairs` and gives
the global implication
`RootRankOneFactorizationStatement.{u} →
RelativeRootRayDecompositionStatement.{u}`.
The rank-one proposition remains an explicit premise.

For a smooth affine group over any field and a monomorphic map from a split
torus, `HasOppositeFactorPairs.rootCoroot` chooses an actual integral
cocharacter for every actual relative root. The published
`exists_rootPoint_actual` supplies a nonidentity rational point of its actual
root subgroup. The pair-existence premise supplies a normalizing opposite
pair, and `IsOppositeFactorPair.coroot_spec` supplies a cocharacter whose
integer pairing with that root is two. The construction uses classical
choice and asserts neither a canonical choice nor a relative-root-system
realization.

For actual roots `a` and `b` with `m • a = n • b` and positive natural
numbers `m,n`, pairing with the two chosen cocharacters gives
`2m = n⟨b,a∨⟩` and `m⟨a,b∨⟩ = 2n` in the integers. Their two cross-pairings
are positive and their product is four, by cancellation of the nonzero
integer `n`. Thus the first cross-pairing is one, two or four. The
corresponding coefficients give `a = 2 • b`, `a = b` or `b = 2 • a`.
Cancellation of a positive natural multiple of characters is justified by
injective rationalization for the split torus and torsion freeness of the
rational tensor space. This argument does not assume a crystallographic
root pairing, root-system finiteness or reducedness.

If both roots are indivisible within the actual root set, either doubling
case contradicts that definition. A common point of two positive integral
rays therefore implies equality of their roots. This proves
`HasOppositeFactorPairs.disjoint_cyclicTail_indivisibleRoots` without any
chosen positive cocharacter.

The final global theorem forgets the extra conclusions of
`HasRankOneFactorization` using the published equivalence with
`HasOppositeFactorPairs`. Connected reductivity supplies smoothness and
affineness, and the actual maximal split torus supplies splitness and the
monomorphic inclusion. Actual-root finiteness follows independently from
the finite-dimensional Lie weight decomposition through
`IsSplitTorus.finite_relativeRoots`. The published
`indivisiblePositiveRootEnumeration` gives the finite injective enumeration;
the new disjointness lemma and the existing positive-ray coverage equivalence
give the rest of the unchanged ray target.

All results preserve arbitrary universes and fields, nonsplit ambient
groups, nonreduced systems and zero or nongeneric cocharacters. The empty
positive-root set is permitted. Indivisibility always refers to division
by another actual root and makes no assertion of primitivity in the full
character lattice.

The provenance is internal composition of the named published root-point,
opposite-pair, lattice, finiteness and ray-enumeration interfaces. This unit
neither constructs opposite factor pairs nor proves the unconditional
rank-one or ray proposition. Any later unconditional application must
supply its geometric premise independently; this conditional result does
not establish that such a dependency route is free of cycles.
