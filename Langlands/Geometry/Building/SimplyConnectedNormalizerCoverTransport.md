# Transport from a simply connected apartment to the actual normalizer image

For actual source data `B : ValuationBuildingData C` and target data
`P : ParahoricBuildingData G` over the same nonarchimedean local field in
arbitrary universe `u`, this module constructs a restriction of the original
target action

`N(F) ∩ G(F)^♮ →* affineWeylGroup P.affineRoots`.

It proves the corresponding conditional image equality and surjectivity.
The supplied comparisons and group-theoretic results remain explicit:

- a homomorphism `f` between the actual source and target normalizer groups;
- an affine equivalence `e : B.Apartment ≃ᵃ[ℝ] P.Apartment`;
- equality of the roots transported along `e` with `P.affineRoots`;
- equivariance `e (m • x) = f m • e x` for the original actions;
- a preimage under `f` for every element of the target normalizer intersection
  with `P.simplyConnectedImage`;
- proofs of `SimplyConnectedFacetFixingStatement.{u}`,
  `IsSimplyConnected C`, and actual source opposite-pair existence.

No forward containment of the range of `f` in the normalizer intersection is
needed. No lifting homomorphism, unique preimages, surjectivity on torus points,
or faithful apartment action is assumed. These hypotheses concern actual
groups, apartments and affine-root sets. The module does not construct them
from a derived cover, and does not assert that the supplied `f` comes from a
specified group-scheme morphism.

The upper-inclusion helper needs only the target AS 3 root-system condition
`IsAffineRootSystemWithRankZero P.affineRoots`. Transport along `e.symm` and
the exact root equality give the same condition on the source. The supplied
facet-fixing proof, source simply-connectedness and actual opposite pairs then
give source normalizer Weyl image via `SimplyConnectedApartmentWeylAction`.
Given a target normalizer element in the simply connected image, take its
supplied normalizer preimage. Apartment equivariance identifies the two original
affine actions by conjugation along `e`. The published affine-Weyl transport
theorem and the root equality carry its source Weyl membership to target
Weyl membership. Rank zero is included.

The equality helper also takes the original target apartment axioms and actual
target opposite-pair existence. Its lower inclusion is the existing result
`affineWeylGroup_le_simplyConnectedNormalizer_map_of_exists_oppositePairs`,
which realizes actual target reflections inside the supplied simply connected
image. Thus the equality helper has the same conclusion as
`SimplyConnectedNormalizerAffineWeylStatement`, with the additional comparison
and existence obligations retained as hypotheses. It is not a proof of that
unconditional published statement.

`simplyConnectedImageNormalizerWeylActionOfComparison` restricts the original
normalizer action using the upper inclusion. Its coercion law is definitional.
Under the target apartment axioms and target opposite-pair existence,
surjectivity uses the existing actual target Weyl representatives; it does not
choose a homomorphic lift through `f`.

This is an internal construction combining affine conjugation, inverse root
transport, the conditional source Weyl action and the existing target
reflection lower inclusion. No new external source assertion or full source
apartment axioms, including AS 5, are introduced.
