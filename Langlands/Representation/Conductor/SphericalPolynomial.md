# The symmetric Laurent polynomial spherical function

This internal development implements the algebraic spherical function used in
Jacquet (2012), Section 2, printed pages 519–520. It builds on the existing
explicit Schur formula in `Langlands.Representation.Whittaker.Spherical`.
The construction and its evaluation identities do not identify a principal-series
Whittaker model or establish an essential-vector or local-factor identity.

The product of the Laurent coordinates is a unit. Multiplying an integral power
of that unit by the Jacobi–Trudi polynomial gives `torusSchur`. Each entry of the
Jacobi–Trudi determinant is a complete homogeneous symmetric polynomial, with
negative indices interpreted as zero. Polynomial renaming commutes with the
determinant, so the resulting Laurent polynomial is fixed by every coordinate
permutation. `symmetricTorusSchur` places it in the actual symmetric subalgebra.
Evaluation recovers the existing complex-valued integral-weight `satakeSchur`.

Unit-tuple evaluations separate Laurent polynomials over an infinite field:
clear the power of the inverted coordinate product and use polynomial
extensionality on the product of the infinite sets of nonzero field elements.
The inverted denominator is a unit, so its cancellation completes the argument.
This also proves extensionality for the symmetric subalgebra.

`sphericalWhittakerPolynomial` is defined on the same Iwasawa cells as the
published complex-valued function. On a dominant cell it is the embedded complex
coefficient `θ(u) halfModulus(q,lam)` times `symmetricTorusSchur(lam)`; it is zero
off those cells. Applying `symmetricTorusEvaluation` at any tuple of complex
units gives exactly `sphericalWhittaker`, without an assumption on `θ`.
If `θ` is trivial on the integral unipotent subgroup, the function has the
displayed dominant-cell and torus values, takes value one at the identity,
transforms on the left by `θ`, and is invariant under the integral group on the
right. These equalities are proved by applying every unit-tuple evaluation and
using evaluation extensionality together with the existing scalar identities.
The field carrying the general linear group is independent of the complex
coefficient field; the construction uses only a valuation and a uniformizing
element, so it also applies in positive characteristic.

The provenance is a derived implementation of Jacquet's introduction of the
`S_(r-1)`-valued spherical function at the end of printed page 519 and beginning
of page 520, Section 2, in *A correction to Conducteur des representations du
groupe lineaire* (2012), source `jacquet-2012-conductor-correction`, SHA-256
`98f02c2aef04bff162c1ceb0a42dd122da746d1304a90d82366a848f22713adf`.
The Lean lemmas here establish the construction and specialization part of that
passage. Its compact-set finite dimensionality, homogeneity, integral transform,
and transform polynomial-finiteness claims are not asserted in this module.
