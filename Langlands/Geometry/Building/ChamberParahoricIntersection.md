# Intersections of actual chamber parahorics

The entry `ParahoricBuildingData.chamberConjugateParahoricEquivCentralizerZeroImage`
is the multiplicative equivalence

```text
(⋂ n : P.normalizerZeroComponent, P.parahoric (n • C))
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

The intersection is the subgroup infimum in the actual rational-point group
`G(F)`. Here `P.normalizerZeroComponent` is the existing subgroup
`N(F) ∩ G(F)^0`, and its action is the original normalizer action on the
apartment. Both directions of the equivalence preserve the ambient rational
point: the construction is `MulEquiv.subgroupCongr` of a proved subgroup
equality. The accompanying application lemma records this property explicitly.

The construction applies to arbitrary universe `u`, every nonarchimedean local
field `F`, the existing actual `ParahoricBuildingData G`, and any chamber `C`.
It retains the following explicit premises:

- The apartment axioms `P.apartment.SatisfiesApartmentAxioms P.centralizer`.
- Actual rank-one factorization `RelativeRoot.HasRankOneFactorization P.i`.
- The global `RelativeRoot.DynamicRootOrderedProductStatement.{u}`.
- The full `P.ChamberIwahoriDecompositionStatement` for these actual data.

The last premise is the published proposition supplying sharp and full
chamber products, their ranges, and their ordered block versions, with its
apartment, chamber-point and generic-cocharacter hypotheses. This module uses
its full-product and depth-zero ordered-block range consequences. It does not
prove that premise or replace it by a weaker geometric assumption.

## Implemented proof

For an actual root element whose depth is nonnegative at every affine Weyl
translate of a chamber point, nonidentity gives a finite root valuation. The
published valuation lemma realizes that valuation at every apartment point by
an extended affine root `psi`. Its value at the original chamber point is
nonnegative and nonzero, hence positive. AS 4 says that `psi` or `2 psi` is an
actual affine root. The affine-root-system coroot gives its reflection as an
element of the affine Weyl group. Evaluating the same root element at that
reflected point would require a nonnegative value, whereas the reflection
formula makes it negative. Thus the root element is the identity. This is
`KPApartmentData.eq_one_of_forall_mem_filtration_affineWeylOrbit`; its own
premises are the affine-root-system and AS 4 consequences, a chamber and a
point in it, and membership in the actual root group.

The ordered-block version fixes any injective enumeration of the indivisible
positive roots for a cocharacter. A point in all the depth-zero block-product
ranges has a tuple of actual root coordinates at the original point and at
each orbit point. Mapping the blocks into the corresponding unfiltered actual
root groups lets the explicit Dynamic ordered-product statement identify all
these tuples. Each original coordinate therefore has nonnegative depth at
every orbit point, so the preceding reflection argument makes it the identity.
The original product is the identity. The proof includes the empty enumeration
and does not require a positive-rank hypothesis or a generic cocharacter for
this auxiliary assertion.

For the full parahorics, choose a generic integral cocharacter of the actual
maximal split torus and a point of `C`. The retained full decomposition writes
a point in the intersection as a negative unipotent factor, the actual image
of a centralizer-zero factor, and a positive unipotent factor. At every affine
Weyl translate of `C`, another such decomposition exists. The private
factor-comparison helper embeds both triples into the full ambient Dynamic
unipotent groups and `centralizerPoints P.i`. The published
`unipotentTripleProduct_injective` identifies the negative and positive
ambient factors. Thus each fixed unipotent factor lies in its corresponding
ordered-block range at every orbit point. The ordered-block argument removes
both factors, leaving the actual centralizer-zero image. Conversely, that
image is contained in the generated full parahoric of every subset. This
proves `iInf_parahoric_affineWeylOrbit_eq_centralizerZeroImage` without using
the rank-one factorization premise.

To pass to the actual restricted normalizer, the published
`affineWeylGroup_le_simplyConnectedNormalizer_map_of_apartment` realizes each
affine Weyl element by a normalizer point in the actual simply connected
image, under the retained rank-one premise. The existing containment of that
image in `P.zeroSubgroup` supplies a point of `P.normalizerZeroComponent`.
Equality of its original affine action with the chosen Weyl transformation
identifies their images of `C`. Membership in every actual normalizer
translate therefore implies membership in every affine Weyl orbit chamber,
so the preceding equality applies. The reverse inclusion again follows from
centralizer-zero containment in every full parahoric. This proves
`iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage` and then the
entry equivalence. The separate membership lemma states the same conditional
saturation implication with a normalizer point and an explicit ambient
zero-subgroup membership premise, matching the form of the published input.

## Provenance and scope

This is derived content from the current Library valuation, affine reflection,
ordered-root-product, opposite-cell injectivity and actual parahoric
interfaces. No new external-source assertion is used. The generated full
parahorics, centralizer-zero image, simply connected image and original
apartment action are retained throughout.

This intermediate unit does not prove
`ChamberConjugateIntersectionStatement` with only its published apartment
premise, or the unchanged `AffineIwahoriTitsStatement`. Their closing proofs
still need to discharge the additional rank-one, ordered-product and full
decomposition inputs and all other obligations of those targets.
