# Domain representations with strict affinoid tests

Author: Worker 36.

`HasImageIn K φ U` means that every bounded multiplicative seminorm on the
actual target algebra pulls back into the subset U. The bounded algebra map
φ goes from P to Q, while its continuous spectrum map goes from M(Q) to M(P).

`Represents K i U` is a proposition about a specified bounded map from a
presented strict affinoid P to a presented strict affinoid Q and a subset
U of M(P). It requires U to be closed, the spectrum image of i to equal U,
and unique bounded factorization through i for every bounded map from P to
any presented strict affinoid R whose spectrum image lies in U. Uniqueness
is equality of actual bounded algebra maps. Each algebra is the constructed
quotient of a finite-variable strict Tate algebra by a closed ideal, and
each spectrum is the actual space of bounded multiplicative seminorms.
The definition does not postulate a representing object.

`RationalData K P` consists only of a finite arity, a denominator, a tuple of
numerators in P, and absence of common spectrum zeros. Its `locus` uses the
inequalities |f_j(x)| ≤ |g(x)|. Its `algebra` and `baseMap` apply the already
constructed rational localization to these actual elements. The algebra is
the closed-ideal quotient of the enlarged finite Tate algebra; the relations
include gY_j = f_j through the existing choice of series representatives.
`spectrumMap` is the continuous pullback of seminorms along `baseMap`.
Neither an inverse denominator, a bounded solution tuple, an output algebra,
nor a factorization property is a field of `RationalData`. This module
constructs its quotient and map but does not yet prove that they represent
its locus.

All coefficient fields are complete ultrametric normed fields. The base,
representing and test algebras use the coefficient universe, with independent
finite arities and ideals. Zero quotients, nilpotents, empty numerator tuples
and trivial scalar valuations are permitted. There is no nontriviality
assumption on an algebra.

The original source is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), Definition 2.2.1 and Exercise 2.2.2(ii), printed/PDF p. 9,
registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Definition 2.2.1 motivates the closed-subset, exact-image and unique
factorization clauses; Definition 2.1.11, p. 8, fixes their contravariant
algebra-map interpretation. Exercise 2.2.2(ii) supplies the rational inputs,
absence-of-common-zeros condition and equations.

This is a derived interface restricted to presented strict affinoid tests and
unit radii. Even the source's term “strictly affinoid domain” requires testing
all affinoid spaces; that stronger property is not named or asserted here.
The construction reuses the enlarged Tate quotient rather than identifying it
with the source's relative power-series presentation. Arbitrary positive
radii, all affinoid tests, the relative-series comparison, structure sheaves,
analytic atlases and sites remain separate obligations.
