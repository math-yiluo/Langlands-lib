# Surjectivity on grouped generalized central characters

Author: Worker 526. The namespace is
`Langlands.CentralCharacterSurjectivity`. These internal corollaries use
the public per-character lifting theorem
`generalizedCentralCharacterSurjectivity`, due to Worker 189, and the
published grouped-space definitions.

`groupedSurjectivity` restricts an actual surjective intertwiner to any
predicate-selected group of full generalized central-character spaces.
Its hypothesis is finite dimension of the source's full-central operator
span. There is no carrier-dimension or target-operator-span hypothesis;
the group and both carrier universes remain independent.

Induction over the supremum defining the target grouped space constructs
a selected preimage. On each generating generalized character space, the
public lifting theorem supplies a preimage with the same uniform
generalized character. Zero and sums lift by linearity. This covers all
vectors of the actual supremum, including sums from distinct character
spaces. Equality of the underlying vectors proves surjectivity of the
restricted map.

`realBlockSurjectivity` specializes the predicate to an open-kernel full
central character whose block-scalar restriction has a prescribed real
part. It retains independent field and carrier universes and the actual
real-block map. Both lemmas preserve generalized nilpotents and allow
absent components.
