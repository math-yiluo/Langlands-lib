# Rational inverse images and bounded base change

Author: Worker 36.

`RationalPullbackStatement` is a proposition about rational data d on a
presented strict affinoid P and a bounded K-algebra map φ from P to a
presented strict affinoid Q. Write A for `d.algebra`, C for
`(d.pullback φ).algebra`, α for the structural map P → A, and β for the
structural map Q → C. Both A and C are the already constructed closed-ideal
Tate quotients of their respective rational input elements.

The first clause asserts that β represents the inverse image of the locus
of d under M(Q) → M(P), with respect to all presented strict affinoid test
algebras. This includes closedness of the inverse image, exact spectrum
image, and unique bounded factorization for those tests.

The remaining clauses assert existence of a bounded map i from A to C with
i ∘ α = β ∘ φ, uniqueness of i among all bounded maps with that equation,
and the following bounded pushout property. Given any complete ultrametric
normed K-algebra B, a bounded map a from A to B and a bounded map b from Q
to B that agree on P, there is a unique bounded map c from C to B
satisfying c ∘ i = a and c ∘ β = b. B occupies an independent universe
and need not be presented affinoid. No `NormOneClass`, nontriviality, or
nonzero-algebra assumption is imposed on B.

The coefficient field is complete and ultrametric; P, Q, A and C use its
universe. All rational radii are one. The statement retains empty numerator
tuples, zero and nonreduced algebras, and trivial scalar valuations. The
only rational admissibility input is the no-common-spectrum-zero field of
d; admissibility of the mapped elements is constructed by `d.pullback φ`.
The map i and the map c are conclusions, not supplied inputs.

This target is derived from Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), Definition 2.1.11, printed/PDF p. 8, and
Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p. 9, registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The source fixes the contravariant map direction and the rational
inequalities and equations. Pulling back these elements gives the inverse
image; their quotient equations motivate the bounded pushout target.

The proposed proof uses rational representation and the equality of the
pulled-back locus with the inverse image for the first clause. For the
bounded pushout, the images under a of the original quotient's fraction
coordinates supply a bounded solution tuple for the mapped equations.
Convergent evaluation descends to C, and uniqueness over Q determines c;
uniqueness over P then gives its required restriction to A. This explains
the derived formulation; this module contains the statement, not its proof.
It does not identify C with a completed tensor product, establish an
all-affinoid-test domain property, compare relative-series presentations,
or construct a sheaf or analytic site.
