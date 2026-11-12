# Integral last-row support of the corrected essential vector

Authors: Worker 1466 and Worker 952.

`essentialIntegralLastRowSupport` proves exactly the published proposition
`Langlands.Conductor.EssentialIntegralLastRowSupportStatement.{uF,uV}`.
The field and representation-space universes remain independent. Every
nonarchimedean local field is included, in any characteristic, and the case
`n = 0` is retained. The target statement, its paired Markdown,
`IsEssentialVector`, `IsJacquetNormalization`, and their imports are unchanged.

The proof unpacks `IsEssentialVector` into its normalized standard L-polynomial
`P`, its essential integral identity, and right integral invariance of the
restriction. The constant coefficient condition `P.coeff 0 = 1` is the first
component of `IsCharacterLPolynomial`. Smoothness comes from admissibility,
which is included in the target's genericity hypothesis.

The helper module `EssentialIntegralSupportSeries` applies the integral
identity to the actual model Laurent series. Finite convolution and scalar
Laurent uniqueness show that this series times the coordinate denominator is
one. Since the denominator has constant coefficient one and polynomial Satake
coefficients, induction from the common lower degree bound proves that every
model degree coefficient is the image of an ordinary multivariate polynomial.

The helper `IntegralLastRowSupportReduction` combines this polynomiality with
the restriction invariance already present in `IsEssentialVector`. Its finite
degree-cell expansion expresses each degree coefficient as a finite dominant
Schur expansion. The algebraic coefficient obstruction proved in
`SchurPolynomialSupport` forces the coefficient of any negative last weight
to vanish. Positive cell mass and the nonzero modulus factors give vanishing
of the Whittaker function at those torus points. The Iwasawa decomposition
then transports a nonzero value at `g` to its torus component. The last
exponent must be nonnegative, and the last row of `g` is the corresponding
integral uniformizer power times the last row of an integral matrix.

These are derived proofs using the published integral expansion, support,
separation and Schur identities. Their implemented route differs from the
degree-of-L-polynomial case split described in the target's source notes.
They assume an essential vector only through the published corrected
predicate, and use no essential-vector existence argument, conductor theorem,
or added compact-subgroup-invariance hypothesis.
