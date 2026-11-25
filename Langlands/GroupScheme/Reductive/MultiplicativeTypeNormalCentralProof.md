# Normal subgroups of multiplicative type are central: proof

This module proves
[`MultiplicativeTypeNormalCentralStatement`](MultiplicativeTypeNormalCentralStatement.md), which
formalizes Conrad, *Reductive group schemes* (2014), Lemma 3.3.1 (pp.96–97). The statement has
three claims:

1. a normal closed subgroup `h : H ⟶ G` of multiplicative type is central;
2. for an fppf quotient `q : G ⟶ Q` by `H` and a central closed subgroup `h' : H' ⟶ Q` of
   multiplicative type, every representative `p : P ⟶ G` of the preimage of `H'` is central;
3. under the same hypotheses, `P` is of multiplicative type.

Conrad derives claim 3 from Corollary B.4.2(2): an extension of a group of multiplicative type
by a group of multiplicative type, with commutative fibres, is of multiplicative type. In the
Library this corollary is the proposition `MultiplicativeTypeFpqcExtensionStatement`.

## Main declarations

- `Langlands.GroupScheme.multiplicativeTypeNormalCentral :
  MultiplicativeTypeNormalCentralStatement.{u}`. This is the unconditional proof of the target
  statement, in every universe `u`, with no extra hypotheses.
- `Langlands.GroupScheme.multiplicativeTypeNormalCentral_of_extension
  (hExt : MultiplicativeTypeFpqcExtensionStatement.{u}) :
  MultiplicativeTypeNormalCentralStatement.{u}`. This is the same argument with Corollary
  B.4.2 taken as an explicit hypothesis, so the reduction to B.4.2 is visible on its own.

## Proof of `multiplicativeTypeNormalCentral`

The theorem applies `multiplicativeTypeNormalCentral_of_extension` to a proof of
`MultiplicativeTypeFpqcExtensionStatement.{u}`. That proof is assembled from published Library
results:

- `ExtensionReduction.fpqcExtension_of_threeStatements` (module
  [`Torus.MultiplicativeTypeCoefficientExtension`](../Torus/MultiplicativeTypeCoefficientExtension.md))
  proves `MultiplicativeTypeFpqcExtensionStatement` from three statements:
  - the fibral criterion `multiplicativeTypeFibralCriterion` (module
    [`Torus.MultiplicativeTypeFibralCriterionProof`](../Torus/MultiplicativeTypeFibralCriterionProof.md));
  - the complete local deformation statement `multiplicativeTypeCompleteLocalDeformation`
    (module
    [`Torus.MultiplicativeTypeCompleteLocalDeformationProof`](../Torus/MultiplicativeTypeCompleteLocalDeformationProof.md));
  - the field case `multiplicativeTypeFieldExtension` (module
    [`Torus.MultiplicativeTypeFieldExtensionProof`](../Torus/MultiplicativeTypeFieldExtensionProof.md)).

All three are proved in the Library, so the composite is an unconditional proof of the extension
statement. The route behind `fpqcExtension_of_threeStatements` is described in its own module
notes. This module only applies it.

## Proof of `multiplicativeTypeNormalCentral_of_extension`

Let `S`, `G` (smooth and affine over `S`, with connected residue fibres) and a closed subgroup
`h : H ⟶ G` of multiplicative type with normal image be given.

- Claim 1 is
  `MultiplicativeTypeNormalCentral.isCentral_of_isNormal_of_isClosedSubgroup` (module
  [`MultiplicativeTypeNormalCentrality`](MultiplicativeTypeNormalCentrality.md)): conjugation is
  a family of endomorphisms of `H` parametrized by `G`, and the family is constant by rigidity.
- Claim 2 is `MultiplicativeTypePreimageCentral.isCentral_preimage` (module
  [`MultiplicativeTypePreimageCentrality`](MultiplicativeTypePreimageCentrality.md)): the
  commutator with `P` descends to a family of homomorphisms `H' → H` parametrized by `G`, which
  is trivial by rigidity.
- Claim 3 applies `SubgroupPreimage.isMultiplicativeType_represented_of_isCentral_inclusion`
  (module [`MultiplicativeTypePreimageReduction`](MultiplicativeTypePreimageReduction.md)) to
  `q`, `h'`, `h` and `hExt`. That theorem applies part 2 of `hExt` to the extension of `H'` by
  `H` given by the actual fibre-product preimage `SubgroupPreimage.groupScheme q h'`. It then
  transfers multiplicative type to `P` along the comparison isomorphism. It needs the actual
  preimage inclusion `SubgroupPreimage.inclusion q h'` to be central. This is again
  `isCentral_preimage`, applied to that inclusion, which represents the preimage functor by
  `SubgroupPreimage.isRepresentedBy_inclusion`. The remaining hypotheses are supplied by:
  - local finite presentation of `H` and `H'`, from
    `RelativeMultiplicativeType.IsMultiplicativeType.locallyOfFinitePresentation`, and
    affineness of `H'` over `S`, from
    `RelativeMultiplicativeType.IsMultiplicativeType.isAffineHom` (both in module
    [`Torus.RelativeMultiplicativeTypeGeometry`](../Torus/RelativeMultiplicativeTypeGeometry.md));
  - the monomorphism property of `h'`, from its being a closed immersion.

This follows Conrad's order: centrality of the preimage first, then commutativity, then
Corollary B.4.2(2).
