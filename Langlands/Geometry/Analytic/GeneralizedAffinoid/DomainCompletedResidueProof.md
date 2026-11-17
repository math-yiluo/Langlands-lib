# Canonical completed residue comparison for full affinoid domains

This module proves the published
`Langlands.Analytic.PresentedAffinoidAlgebra.DomainCompletedResidueSurjectivityStatement`
as `domainCompletedResidueSurjectivity`. The field universe is arbitrary.
The full `Represents` hypothesis is retained, with arbitrary finite positive
polyradii and trivially normed coefficient fields allowed.

## Implemented proof

First, `Represents.eq_of_comp_eq` extends uniqueness from presented affinoid
tests to any complete ultrametric normed commutative coefficient algebra.
The published `finiteJointImage` factors two bounded maps through a single
presented affinoid test with an injective map into the complete target.
Their equality on the base algebra descends to this test. Its spectrum map
has image in the represented locus, so the full domain property gives equality
of the two maps in the test, hence equality in the original target.

At a point `y`, let `F` and `E` be the completed residue fields of the base
point and `y`. Give `E` its `F`-algebra structure using the actual canonical
map `completedResidueComap`. Its isometry makes this a normed algebra.
The injective map from `E ⊗[F] E` into its ultrametric projective tensor
completion is contractive on pure tensors, so its two factor maps give
bounded maps from the domain algebra into a complete ultrametric normed
algebra. Canonical compatibility with base evaluations makes their composites
with the base map equal. The preceding uniqueness lemma equates them.
Injectivity of the tensor map then gives `e ⊗ 1 = 1 ⊗ e` for every residue
value `e` of an element of the domain algebra. The published algebraic
equalizer lemma `FieldTensor.mem_range_of_tmul_eq` puts each such value
in the image of the canonical residue map.

Finally, fractions of original-algebra residue values also lie in the image,
since the map is a field homomorphism. These fractions form the normed
residue field whose completion is `E`. The image of the complete field `F`
under the canonical isometry is closed. Completion induction therefore
puts every element of `E` in the image, proving surjectivity.

## Provenance and scope

This is an internal derivation of the unchanged published target. Its
original-source correspondence is documented in
`DomainCompletedResidueStatement.md`: Berkovich's canonical completed
residue comparison and full affinoid-domain universal property.
The implementation combines the published finite joint image construction,
the tensor argument already used in `StrictTestDomain.FibreComparison`,
the all-norm tensor construction in `ValuedField.SeparatedTensor`, and the
canonical completed residue-field construction. It uses the full affinoid
test property; no complete field is assumed to be a presented affinoid test.
The proof concerns the existing canonical map and introduces no additional
tensor, nontrivial-valuation, or strictness premise.
