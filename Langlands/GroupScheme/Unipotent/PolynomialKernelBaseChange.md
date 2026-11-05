# Actual scalar extension of additive polynomial kernels

## Scope and provenance

This internal construction identifies the actual scheme base change of the
kernel of a separated additive polynomial row with the actual kernel of the
coefficientwise extended row. The fields and their spectra have the same
arbitrary universe, as required by the existing scheme base-change functor.
There is no restriction on characteristic, perfection, finiteness of either
field, or degree of the extension for the isomorphism itself. The constancy
comparison requires an algebraic Galois extension (`IsGalois`); it does not
require a finite extension.

The construction is derived from the existing actual polynomial-row maps,
natural vector-group coordinates, the spectrum/global-functions adjunction,
and the multiplicative pullback point equivalence in `KernelBaseChange`.
It asserts no presentation for an arbitrary unipotent group and adds no
smoothness, connectedness or unipotence conclusion about the polynomial
kernel or its complement.

## Definitions and implemented proof

`structureMap_map_algebraBaseMap` proves that regarding a scheme over the
extension field as a scheme over the original field composes its global-function
structure map with the coefficient homomorphism. This follows from naturality
of the spectrum/global-functions isomorphism and functoriality of global
sections. `comp_polynomialRow_eq_one_iff` expresses the actual pointwise kernel
condition as vanishing of the sum of polynomial evaluations.

`scalarVectorPointsEquiv` identifies vector-group points by their natural
coordinates in the global functions of each relative scheme test. The underlying
test scheme is unchanged by forgetting the extension field. Evaluation of a
mapped polynomial equals evaluation of the original polynomial under the
composite structure map, so this comparison preserves the kernel condition.
`scalarKernelPointsEquiv` is its restriction to the pointwise kernel subgroups.
Both comparisons are natural on every relative scheme test, including tests
that are not affine.

`polynomialKernelBaseChangePointsEquiv` composes the actual base-change point
equivalence, the canonical kernel point equivalence, the scalar pointwise
kernel comparison, and the inverse canonical kernel point equivalence over
the extension field. The lemma with suffix `_kernelPoints` records its
compatibility with these kernel identifications; its naturality follows from
the naturality of the three constituent comparisons.

`polynomialKernelBaseChangeIso` applies the existing `isoOfPoints` construction
to this natural multiplicative equivalence. Thus it is an isomorphism of actual
group schemes. `comp_polynomialKernelBaseChangeIso_hom` states exactly the
induced map on every test scheme.

## Consequences

`hasConstantAffineLineMaps_baseChange_polynomialKernel_iff` transports actual
affine-line constancy along this isomorphism in both directions, using
`HasConstantAffineLineMaps.of_mono`. The existing coefficientwise Galois
invariance theorem from `PolynomialKernelCriterion` then gives invariance
under actual scheme base change.

`exists_polynomialKernelVectorFactor_separableClosure` combines this result
with the finite iteration in `PolynomialKernelVectorFactor`. For a row of
length `n`, it gives numbers `r,m` with `r+m=n`, another additive row of length
`m`, and an actual isomorphism of the original kernel with the product of the
standard vector group of dimension `r` and the new kernel. The new kernel has
only constant actual affine-line maps over the original field and after actual
base change to its separable closure. The last step uses the existing Galois
instance for the separable closure. It does not supply the separate structural
presentation needed to apply this statement to arbitrary unipotent groups.
