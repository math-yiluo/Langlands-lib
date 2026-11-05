# The simply connected normalizer action from facet fixing

For actual `ValuationBuildingData G` over a nonarchimedean local field in
arbitrary universe `u`, this module constructs a homomorphism from the
normalizer of its maximal split torus to the actual affine Weyl subgroup.
Its underlying affine action is the original normalizer action, and it is
surjective.

The construction has four explicit proof parameters:

- `SimplyConnectedFacetFixingStatement.{u}`;
- `IsSimplyConnected G`;
- `IsAffineRootSystemWithRankZero B.affineRoots`, the AS 3 root-system condition;
- `RelativeRoot.HasOppositeFactorPairs B.i`, existence of the actual rank-one
  opposite-factor pairs.

In particular, the module does not prove the facet-fixing statement or
opposite-pair existence. It assumes no apartment-axiom bundle or AS 5 for the
simply connected group. The supplied building data already contain full
omega compatibility.

The first helper proves equality of the normalizer's affine image with the
affine Weyl subgroup from the local condition that every normalizer element
stabilizing an actual facet fixes it pointwise. It applies the generic
facet-fixing reduction of `FacetFixingWeylReduction` to the actual normalizer
action. Root preservation comes from `NormalizerAffineRootAction`, without
apartment axioms. The lower inclusion comes from actual opposite-pair
reflections and coroot uniqueness under the stated AS 3 condition. The generic
reduction uses a regular point and chamber, Weyl chamber transitivity, and
affine-span rigidity to prove the upper inclusion. Rank zero is included.

The next helper specializes this result using the supplied proof of
`SimplyConnectedFacetFixingStatement` at the given field, group and building
data. Its conclusion is exactly the simply connected image equality in the
second sentence of AS 5; the remaining AS 5 clauses are not asserted.

`simplyConnectedNormalizerWeylAction` restricts the codomain of the existing
normalizer homomorphism using that equality. Its coercion and evaluation laws
are definitional. Surjectivity follows by reading membership in the original
homomorphism's range and retaining the same preimage. No faithfulness or
injectivity of the normalizer action is asserted.

This is an internal construction obtained by composing the named results and
restricting a homomorphism's codomain. It claims no additional theorem from
external literature. It is a conditional step toward
`SimplyConnectedNormalizerAffineWeylStatement`, whose unchanged final target
concerns the normalizer intersection with the simply connected cover image of
a general connected reductive group; that final statement is not proved here.
