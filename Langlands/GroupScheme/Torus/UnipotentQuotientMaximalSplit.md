# Maximal split tori through smooth connected unipotent quotients

This is an internal consequence of the published field-group torus lifting,
unipotent-kernel closedness and rational conjugacy proofs. It concerns actual
represented quotients and retains the given source torus and quotient map.

Let `k` be a perfect field of arbitrary characteristic, let `G` and `Q` be affine
group schemes locally of finite type over `k`, and let `n : N ⟶ G` be a closed
embedding with `N` smooth, connected and unipotent. Suppose `q : G ⟶ Q` satisfies
the existing `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) q`.
`PerfectFieldUnipotentQuotientMaximalSplitTorusStatement` asserts:

- For every commutative group scheme `T` and map `i : T.toGrp ⟶ G`,
  `i ≫ q` is a maximal split torus if and only if `i` is.
- Every specified maximal split torus `j : T.toGrp ⟶ Q` has a lift
  `i : T.toGrp ⟶ G` with `i ≫ q = j` and `i` maximal split.
- The existing split ranks, valued in `ℕ∞`, satisfy `splitRank G = splitRank Q`.

The field and all group schemes lie in arbitrary universe `u`. Neither ambient
group is assumed reductive, smooth or connected. The quotient hypothesis
includes fppf flatness, surjectivity, local finite presentation and equality of
the represented full scheme-theoretic kernel with the range of `n`.

## Implemented proof

Source isomorphisms preserve splitness, closedness and the factorization
definition of maximality. Combining this with the published ambient-isomorphism
transport `IsMaximalSplitTorus.comp_iso_iff` proves
`SubgroupConjugate.isMaximalSplitTorus_iff`.

The generic lemma `IsMaximalSplitTorus.comp_of_split_torus_lifts` assumes that the
image is closed, all closed split tori downstairs lift homomorphically with
their original source, and maps from the original torus with equal quotient
composites are rationally subgroup-conjugate. Lift a proposed larger split
torus. The lift is monomorphic because its quotient composite is a closed
embedding, so `IsTorus.isClosedSubgroup_of_mono` makes it closed. Conjugacy
transports the original maximality to the factor through this lift. Applying
that maximality shows the proposed factor is an isomorphism.

For the supplied quotient, closedness follows from
`IsUnipotent.closed_torus_quotient` and the published
`unipotentClosedSubgroup` proof. The full kernel is contained in the unipotent
range by the exact equality in the quotient hypothesis. The published
`IsTorus.exists_splitUnipotentQuotientLift` supplies homomorphic lifts, using
`RelativeRoot.splitUnipotentStableVectorSubgroup` and
`RelativeRoot.torusVectorActionLinearization`. Equal-map conjugacy is supplied
by
`subgroupConjugate_of_isTorus_fppf_split_unipotent_kernel_of_structuralStatements`,
using those same two proved inputs and `splitUnipotentAffineTorsorStatement`.
This proves preservation when the kernel is split unipotent.

Reflection requires no perfectness or splitness of the kernel. If `i ≫ q` is
maximal split, its source is split and `i` is monomorphic. The same closedness
theorem for monomorphic torus maps makes `i` closed. Every proposed larger split
torus upstairs maps to a closed split torus downstairs by the unipotent-kernel
closedness theorem. Downstairs maximality then forces the original factor to
be an isomorphism. This is
`IsMaximalSplitTorus.of_comp_of_unipotent_kernel`. The statement of this helper
only assumes that the full kernel is contained in an affine locally finite
type unipotent range, together with affine locally finite type ambient groups.

To lift a specified maximal split torus, use the same published torus lift and
then apply reflection. The map back to the quotient is exactly the original
embedding, with no source replacement. For split-rank equality, map each finite
split torus upstairs to the quotient for one inequality; lift each finite split
torus downstairs for the other. In each direction `card_le_splitRank` bounds the
same finite index type, and the supremum definition of split rank finishes.

Finally `perfectFieldUnipotentSplit` makes the represented smooth connected
unipotent kernel split over a perfect field. This discharges the splitness
premise in preservation, lifting and split-rank equality.
`perfectFieldUnipotentQuotientMaximalSplitTorus` assembles the three conclusions
of the Prop-valued statement.

## Published inputs and scope

The direct import is
`Langlands.GroupScheme.Torus.UnipotentQuotientMaximal`. Its imports provide the
torus lifting and equal-map conjugacy theorems named above,
`Langlands.GroupScheme.Torus.UnipotentQuotientClosed`,
`Langlands.GroupScheme.Torus.MaximalTransport`, and
`Langlands.GroupScheme.Rational.SplitRankTransport`. The result for full maximal
tori in that imported module alone does not imply this statement: a maximal
split torus need not be a maximal torus.

This contribution supplies only field-group algebra for comparing split tori
of a neutral special fibre and its reductive quotient. It constructs no
integral model, lifts no torus over a valuation ring, proves no Galois-facet
or residue-parabolic correspondence, and does not prove
`Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement`.
