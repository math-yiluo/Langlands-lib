# Actual refined tensor Jacquet occurrences

Author: Worker 19.

This internal adapter bundles the existing actual upper normalized refined
Jacquet tensor equivalence as a smooth isomorphism. It preserves every coarse
block, the supplied topology, and independent field and carrier universes.
It does not establish local rank-three structure or either repeated-factor
transfer.

`refinedJacquetExternalIso` identifies the actual refinement of an external
coarse tensor with the external tensor of its actual normalized block Jacquet
modules, pulled back along the inverse continuous refined-Levi equivalence.
Its underlying equivariant linear equivalence is exactly
`RefinedJacquetTensor.jacquetEquiv`.

`subquotient_refinedJacquet_external_iff` transports an actual smooth
subquotient along this isomorphism, then preserves or reflects the common
group pullback. `subquotient_factor_of_refinedJacquet_external` applies the
existing actual smooth tensor-factor extraction to that occurrence and
requires irreducibility of each constituent block representation.
`subquotient_refinedJacquet_external_of_factors` tensors actual presenting
spans, then transports the resulting occurrence back through the same
comparison. The return direction needs no irreducibility, admissibility,
finite length or dimension assumption.

The constituent and ambient carriers lie in `Type uV`, independently of the
field universe `uF`; specializing `uV` to `max uF uV` gives the host task's
carrier scope. The refinement and each block shape are arbitrary. In
particular, the adapter neither drops outside blocks nor imposes support or
cuspidal-line conditions on them. The private ring-topology proof derives
`IsTopologicalRing` from the supplied `T.topology`, `T.valuativeRel` and
`T.localField`; it introduces no additional topology hypothesis.

## Dependency audit

The construction is internal algebra of existing actual quotient modules and
actual subquotients, with no external source assertion. Its two direct
imports are `Tensor.SmoothSubquotients` and
`Parabolic.RefinedJacquetTensor`. A recursive traversal at Library base
`125fca1a70e8f89af98a36c8565617cd68f73be5` contains 155 project modules,
including this one. The classification-named modules are exactly
`CanonicalConstituents`, `ConstituentRelations`,
`CuspidalJacquetMultiplicityStatement`, `Essential`,
`RelativeGenericityStatement`, `RelativeJacquetMultiplicityStatement`,
`RelativeRegularComparisonStatement`, `Segments`, `Supercuspidal`,
`SupercuspidalSupport`, `SupercuspidalTwist`, `Tempered`,
`TemperedInductionStatement`, and `TemperedSupportStatement`.

The actual proof bodies used here give the following dependency route:

- `RefinedJacquetTensor.refinedCoinvariantsEquiv` specializes the existing
  product-subgroup coinvariant equivalence to the upper block radicals,
  then applies the actual block Jacquet carrier equivalences. The
  product-subgroup result in `RefinedOppositeJacquetTensor` is untwisted
  algebra despite that module's name: it takes every character to be one.
- `Tensor.CharacterLocalization` constructs its forward map by tensoring
  quotient projections. Its inverse descends the pure-tensor quotient map
  through each slot's relation submodule. The product subgroup's individual
  coordinate elements give the required kernel containments. Checking pure
  tensors proves that the descended maps are inverse. No exactness,
  finite-length, support or classification theorem enters this route.
- The upper normalized equivariance proof uses the inverse half of the
  product Levi modulus. `RefinedInductionTensorNormalization` proves the
  corresponding half-modulus product by applying the square-root character
  and its complex coefficient map to a finite product.
  `refinedLeviInverseHalfModulus_eq_prod` then takes inverses. On pure
  tensors the scalar product is exactly the product of the block inverse
  halves. The actual refined Levi coordinates embed back into the original
  coarse blocks; quotient representatives and tensor induction finish
  equivariance for all vectors.
- `Tensor.SmoothSubquotients` supplies the actual quotient-by-kernel bridge,
  common group-pullback preservation and reflection, tensor reassembly of
  actual injective/surjective spans, and irreducible factor extraction.
  Extraction restricts to one coordinate and uses contraction in the
  trivially acted complementary tensor, with a minimum-dimensional
  nonzero complementary support and quotient descent. Reassembly uses
  linear splittings to prove tensor-map injectivity and surjectivity.
- The common smooth group pullback keeps the actual carrier and
  precomposes its action. Its smoothness comes from inverse images of
  open stabilizers. `SmoothRep.mkIso` bundles the existing equivariant
  linear equivalence, and the existing actual-subquotient isomorphism
  transports change only its presenting injection or surjection.

The classification-named imports provide definitions, statement interfaces
and elementary actual-subquotient algebra, rather than any of the excluded
classification conclusions. This adapter uses no global support
decomposition, general ordered quotient coverage, multisegment
classification, geometric-lemma calculation, Jacquet finite-length theorem,
or local cuspidal-product structure. The checked route is therefore directly
and transitively independent of the eight classification tasks excluded by
the host contract and their proof successors.

Development compilation and inspection of `refinedJacquetExternalIso`
succeed without errors or warnings, retain the two independent universe
parameters, and use only `propext`, `Classical.choice` and `Quot.sound`.
These development checks do not establish independent semantic acceptance
or either final repeated-factor transfer.
