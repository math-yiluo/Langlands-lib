# Full-normalizer normality and the descended actual apartment action

This internal derived construction works with the original
`ParahoricBuildingData P` in an arbitrary field universe. Under the explicit
cover comparison `P.zeroDatum.CoverImageCentralizerNormKernelStatement`, it
identifies `P.normalizerZero` with the intersection of
`P.normalizerZeroComponent` and the kernel of the actual full normalizer action
on the apartment. Consequently, if `P.zeroSubgroup` is normal in the ambient
rational-point group, `P.normalizerZero` is normal in the full normalizer.
Normality of the ambient zero subgroup and the cover comparison remain inputs
to this implication.

Every original centralizer-zero element acts trivially by omega compatibility
and the centralizer norm-kernel inclusion. This unconditional inclusion gives
one direction of the intersection equality, together with the published
inclusion into the zero-component normalizer. The converse is the exact
restricted action-kernel theorem: under the cover comparison, a zero-component
normalizer point acting trivially is centralizer-zero. The zero-component
normalizer is the pullback of the ambient zero subgroup along the normalizer
inclusion. When the ambient subgroup is normal, its pullback is normal; the
kernel of the full action is normal as well. Their intersection therefore
proves the stated full-normalizer normality.

`iwahoriWeylApartmentAction` descends the actual normalizer homomorphism to the
original quotient `P.IwahoriWeylGroup`. Its definition requires the quotient's
normality instance and uses the unconditional centralizer-zero kernel
inclusion; it needs no cover comparison. Its value on every quotient
representative is exactly the original affine normalizer action.
`affinePartApartmentAction` restricts this homomorphism to the original
`P.affinePart`, again with the literal action on representatives.

Under the cover comparison, this restricted descended action is injective.
A kernel element of the affine part has a representative in the actual
zero-component normalizer. Its trivial action puts the representative in
`P.normalizerZero`, so its original quotient class is the identity. The
group-homomorphism kernel criterion proves injectivity.

The provenance is deduction from the actual subgroup and quotient definitions,
omega compatibility, the conditional exact action-kernel theorem, and standard
pullback and intersection normality. No external source assertion is
introduced. The unconditional ambient zero-subgroup normality, the cover
comparison, the image comparison with the geometric affine Weyl group, and the
closing affine Iwahori–Tits statement remain separate obligations.

The subgroup inclusion `normalizerZero_le_ker_normalizerAffineEquiv` reuses
`normalizerAffineEquiv_eq_one_of_mem_normalizerZero` from
`IwahoriWeylExactSequenceReduction`; its pointwise proof is unchanged.
