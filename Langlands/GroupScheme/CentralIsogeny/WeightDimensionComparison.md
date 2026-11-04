# Nonzero weight comparison from dimension equalities

This is an internal linear algebra consequence of the Library's actual
split-torus adjoint weight decomposition and its differential calculation for a
central full scheme-theoretic kernel. It has no additional literature claim.

Let `k : Type u` be any field, let `G` and `H` be affine group schemes locally
of finite type over `Spec k`, and let `q : G ⟶ H` have central full kernel.
Let the split commutative torus `T` act through `i : T.toGrp ⟶ G`.
Assume explicitly that:

- `Lie.dimension G = Lie.dimension H`;
- the zero-weight spaces for `i` and `i ≫ q` have equal `k`-finrank.

`Lie.weightSpaceMap_surjective_of_dimensions` proves that the actual
differential restricted to the weight space of every nonzero character is
surjective onto the corresponding target weight space.
`Lie.nonzeroWeightSpaceEquivOfDimensions` combines this with the published
nonzero-weight injectivity theorem to give a linear equivalence. Its coercion
formula is the original differential `Lie.targetMapLinear q k`.
`roots_comp_eq_of_central_kernel_of_dimensions` proves equality of the two
actual root sets, with both viewed in the character lattice of the same `T`.

The proof uses the published internal direct-sum decompositions of `Lie G`
and `Lie H` into their actual character weight spaces. These decompositions
transfer finite dimensionality and the total dimension equality to the direct
sums. Equal zero-weight dimensions provide an arbitrary linear equivalence
between the zero blocks. On every other block use the actual differential,
which is injective by `Lie.weightSpaceMap_injective_of_central_kernel`.
The resulting direct-sum linear map is injective. Equal finite dimensions
make it surjective, and surjectivity of a direct-sum map implies surjectivity
on each block. At every nonzero character the block is the original
differential. Finally, a nonzero target weight space has a nonzero source
weight space by this surjectivity, while the published central-kernel root
inclusion gives the other direction.

The auxiliary direct-sum map is used only inside the proof. Its zero block
is arbitrary; the theorem makes no claim that the differential is surjective
on the zero-weight space.

The dimension equalities remain hypotheses. This module does not prove them
for isogenies or maximal tori. It also does not compare character lattices of
different tori, prove normalizer-image finiteness or coroot compatibility,
or prove `CentralIsogenyRootDatumHomStatement`. No smoothness, separability,
characteristic or perfection assumption is added to the stated conditional
comparison.
