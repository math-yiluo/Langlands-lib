# Actual maximal tori and roots of split-torus centralizers

Author: Worker 1352.

This internal construction combines published torus extension, split-torus
centralizer, central-root restriction, and dynamic Lie comparisons. It does
not construct root data or compare derived coroots.

For an affine group locally of finite type over an algebraically closed field,
a split subtorus `a : A.toGrp ⟶ G`, and any all-test centralizer representative
`j : M ⟶ G`, `splitTorusCentralizerRootModel` chooses a commutative split torus
`T`, maximal-torus embeddings into `G` and `M`, and a closed map `A ⟶ T`.
Both morphism squares commute. The constructor extends `A` to an ambient
maximal torus using `exists_maximalTorus_extension_of_finiteType`, splits that
torus using finite Galois splitting over an algebraically closed field, and
factors its inclusion through `j` by the all-test range containment.
The type-valued model is chosen by classical choice from the resulting
nonempty model type. Closedness of the supplied representative is proved by
`IsSplitTorus.isClosedSubgroup_torusCentralizer`; it is not an added premise.
Maximality in `M` follows from ambient maximality by `IsMaximalTorus.of_comp`.

The generic theorem `relativeRoots_splitTorusCentralizer_factor` works over
any field, with affine locally finite-type `G` and `M` and supplied compatible
torus maps `i`, `iM`, and `f : A ⟶ T`. It identifies the actual roots of `iM`
with ambient roots `α` satisfying `f ≫ α = 0`. The forward implication uses
the injective Lie map and centrality of the canonical factor of `A` in `M`.
For the reverse implication, it postcomposes `centralizingCocharacter` by `f`,
identifies its dynamic centralizer with the given torus centralizer, and
applies `relativeRoots_centralizer_factor` with the proved `dynamicLie`.
The zero restriction makes the integral pairing with this cocharacter zero.

The model's `cocharacter_centralizer` records the equality of all-test
centralizer subgroup functors. Its `relativeRoots_eq` and
`relativeRoots_eq_pairing` give respectively the zero-restriction and
zero-pairing descriptions on the actual character lattice. These root
comparisons use affineness and local finite type of `M` as typeclass
assumptions; for a supplied centralizer of an affine locally finite-type
group, both follow from its proved closed immersion into `G`.

The unit's provenance is the explicit composition of these existing Library
results. No new external structural assertion is assumed. It supplies
geometric input toward `SplitTorusCentralizerDerivedCorootComparisonStatement`;
actual root-datum existence, the derived torus and coroot comparison, and
the choice of a base with the required integral span remain separate work.
