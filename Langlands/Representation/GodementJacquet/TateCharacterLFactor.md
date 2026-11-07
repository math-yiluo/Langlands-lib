# Exact character Euler polynomials for matrix and JPSS values

This internal derived module transports the scalar normalization proved in
`TateCharacterNormalizer` to the actual rank-one matrix value families and to
the JPSS L-polynomial relation for a pair of continuous characters.
The field is an arbitrary `PadicField` at every prime, with its canonical
topological data; the field and representation-carrier universes are
independent.

For a smooth nonzero representation on which a specified character acts by
scalars, equality of actual matrix and scalar rational-value families
identifies the matrix normalized generator with `PadicAbelian.lPolynomial`.
The inverse-transpose value family has the inverse-character polynomial.
Combining these exact generators with the existing convergence and rationality
theorems gives both complete analytic predicates with the specified polynomials.

Scalar action passes to each actual Whittaker coefficient image through the
surjective linear intertwiner `modelMap`. A nonzero functional produces a
nonzero image vector by evaluation at the identity. For a representation of
full rank-one Whittaker type, the functional line supplies such a functional.
The published comparisons between JPSS values, matrix–Whittaker values and
ordinary matrix coefficients identify their Laurent spans. The exact matrix
generator therefore proves the standard JPSS L-polynomial relation at every
compatible quotient measure.

For characters `χ` and `η`, the determinant twist of the first character
representation by `η` is the representation of `χ * η`. The published twist
identity then identifies the pair polynomial with the abelian polynomial of
that product character. Compatible quotient-measure existence is supplied by
the actual normalized Haar construction. The additive Haar measure is
arbitrary. The additive character ranges over continuous, nontrivial
unit-circle-valued characters; nontriviality is bundled in
`HarmonicAnalysis.UnitaryAdditiveCharacter`.

`RankOneCharactersLPolynomialStatement F` states this last assertion universally
over both continuous multiplicative characters, every continuous nontrivial
unit-circle-valued additive character and every additive Haar measure. The theorem `rankOneCharactersLPolynomialStatement` proves this
proposition by the preceding explicit certificate; it adds no hypothesis.

The nonzero image-vector argument follows the evaluation-at-one argument in
Worker 929’s `ModelGenericSocleProof`. The span transport is the reverse of the method
implemented by Worker 468 in `ModelMatrixNormalizedGenerator`.

The provenance is internal: the scalar normalized generator, exact canonical
Haar transport, coefficient-image construction, published Whittaker span
comparisons and determinant-twist invariance. This module does not establish
analytic epsilon compatibility or the closed supercuspidal correspondence.
