# Directed covers for actual standard rational-point induction-Jacquet

Worker 194 supplies this internal construction and specialization of the published directed-cover
and rational unipotent-regularity theorems. The ambient group is literally
`RationalPoint k G.X`, with its canonical evaluation topology `pointTopology`.
The standard index is a finite subset `K` of the actual subtype `SimpleRoot i ν`;
the parabolic, Levi and unipotent subgroups are the published `parabolic i ν K`,
`levi i ν K` and `unipotent i ν K`. No group, topology or normalized functor is
replaced.

`standardInductionJacquetFunctor_exists_preimage_of_directed_cover` considers
an arbitrary family of actual smooth complex representations `A j` mapping
injectively into `B`. Their actual invariant ranges must be directed by
inclusion and must contain every vector of `B`. The theorem proves that each
vector of the actual normalized composite `i_K r_K B` is the image of a vector
in `i_K r_K (A j)` for some single stage `j`, under the composite functor's
actual map. No transition maps between stages are required. The field universe
`u`, additional representation universe `v`, and indexing universe `w` are
independent. The representation carriers have universe `max (u + 1) v`, as in
the full rational support target.

`standardInductionJacquetDirectedLift` chooses such a stage and vector. Its
value is a dependent pair of the stage index and an actual vector in that
stage's composite, bundled with the proved equation that its image is `f`.
The construction uses classical choice on the preceding existence theorem;
the bundled property provides the exact map equation to consumers.

The hypotheses are a nonarchimedean local field `k`, an affine group scheme
`G`, a commutative group scheme `T`, the maximal split torus homomorphism
`i : T.toGrp ⟶ G`, and the generic cocharacter `ν`. Connected reductivity,
maximal splitness and genericity are supplied as their existing predicates.
`StandardCocharacterStatement.{u}` remains an explicit premise, as in the
support target. The point group is locally compact and nonarchimedean at the
canonical topology, and the actual standard unipotent subgroup has the supplied
closedness proof `hU`. Compactness of the actual left quotient
`Induction.LeftQuotient (parabolic i ν K)` is an explicit intermediate hypothesis.
There are no finite length, admissibility, finite dimension or finite generation
restrictions on the representations or the family.

The implemented proof applies
`General.inductionJacquetFunctor_exists_preimage_of_directed_cover` to the
published
`RationalPointFamily.isSemidirectDecomposition_of_standardCocharacterStatement`.
Its compact-limit requirement is discharged by the exact theorem
`RationalPointFamily.standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
from the same `i`, `ν`, `hStandard`, `hG`, `hi`, `hν` and `K`. Thus this helper has
no additional compact-limit premise. The generic directed-cover proof chooses
representatives in the actual Jacquet quotients, uses compact-limit injectivity
of normalized Jacquet maps, and lifts induced functions through one coefficient
image using a finite double-coset cover of the compact quotient. The rational
compact-limit theorem transports the published dynamic unipotent compact
containment theorem along the actual standard-cocharacter subgroup equality.
These are the declaration-level mathematical inputs, beyond the existing
normalized objects and maps imported by those two modules. This internal
composition invokes no classification, character-independence, geometric-lemma
or adjointness theorem in its proof; unrelated declarations in imported modules
are not additional proof inputs.

This is an arbitrary-directed-family helper. It does not construct a finite-span
exhaustion or assert support compatibility of any stage. It does not prove
`RationalSupportCategoryInductionJacquetStatement`: quotient compactness still
requires a proof from that statement's data, and preservation of the support
category requires a representation-theoretic argument in addition to exhaustion.
The target and all imported Lean/Markdown pairs are preserved.
