# Standard fixed-vector Jacquet lift from the generalized Jacquet lemma

This is an internal conditional adapter. It retains
`GeneralizedJacquetLemmaStatement` as an explicit prerequisite and supplies no
proof of that VI.9.1 statement or of either VI.9.4 statement. Field and
representation carrier universes remain independent.

For a connected reductive group over a nonarchimedean local field, fix a maximal
split torus, a generic cocharacter, one standard index, one cocharacter standard
for that index, and a compatible split component. Let `K` be compact and open in
the canonical rational-point topology, and assume the pointwise predicate
`StandardParabolicBasisMember` for that component and `K`. The theorem
`standardFixedJacquetMap_surjective_of_generalizedJacquet` derives surjectivity of
the published `fixedJacquetMap` onto the `K ∩ M` fixed vectors of the actual
unnormalized standard Jacquet action, for every smooth complex representation.
There is no admissibility or finite-dimensionality assumption.

The standard Levi and radical equal the dynamic centralizer and radical of the
supplied standard cocharacter. Their comparison uses the published unconditional
`relativeRootNegation` and standard/dynamic comparison. The lemma
`standardOppositeUnipotentPoints_eq_dynamic` supplies the opposite comparison:
negate the chamber, the index and the standard cocharacter, apply the same
comparison, and identify the resulting dynamic radical with that of the inverse
cocharacter. Neither comparison assumes global standard-cocharacter existence
or a relative-root-system statement.

The compatible component's `centralStrictElement` proves centrality in this same
Levi, and its pointwise contraction theorem gives `IsIwahoriContraction` for `K`.
The canonical topology agrees definitionally with the topology of the generalized
lemma. The local-field and connected-reductive data supply its Hausdorff,
local-compactness and nonarchimedean instances. After transporting the three
subgroups by the comparisons, the assumed generalized Jacquet lemma applies.
Proof irrelevance identifies the two normalizer proofs in the fixed-vector map.

The definition `standardFixedJacquetLift` chooses a complex-linear right inverse
of this surjective map using projectivity of vector spaces. The theorem
`fixedJacquetMap_comp_standardFixedJacquetLift` gives its exact right-inverse
identity. This choice asserts no canonical section, equivariance, compatibility
between different `K`, or uniform bound.

The provenance is internal: the module composes the published standard and
dynamic subgroup comparisons, the compatible-component central contraction,
the existing fixed-vector map, and Mathlib's splitting of a surjective linear
map onto a projective module. The only representation-theoretic prerequisite
added to the local data is the explicitly named generalized Jacquet lemma.
