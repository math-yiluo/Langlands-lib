# Segment polynomials, the monomial basis target and Zelevinsky's endomorphism

This module works with the actual graded exact-K0 carrier and actual induction
multiplication from `GradedGrothendieck`. Its explicit parameters are a proof
of `BinaryProductExactnessStatement` and a proof of
`GradedInductionRingLawsStatement`. Thus the ring structure is the
constructed induction ring, with its actual rank-zero unit. Coefficients are
complex representations and integral K0; `F,T` are the current `PadicField`
models, with independent field and saturated carrier universes.

`segmentPolynomialEvaluation` evaluates integer multivariate polynomials in
the published segment type at `gradedSegmentSocle`, the actual class of the
increasing segment socle. `SegmentPolynomialComparisonStatement` is the
precise missing bijectivity target corresponding to Zelevinsky 1980,
Corollary 7.5, printed p.193. It is a comparison with actual K0, not a
replacement of K0 by a free label lattice.

`segmentMonomial` evaluates a monomial with coefficient one; its index is a
finite multiplicity function on segments, equivalently a finite multiset.
The zero multiplicity function is the empty product, hence the graded unit.
`SegmentMonomialSpanningStatement` requires these monomials to span the
whole actual graded K0 over the integers.
`SegmentMonomialBasisStatement` additionally requires their integer-linear
independence. These statements concern all monomials in the segment
generators. They do not assert that the individual generators themselves
form an additive basis.

Given a proof of the polynomial comparison,
`segmentPolynomialEquiv` constructs the exact comparison ring equivalence,
and `segmentMonomialBasis` transports the ordinary polynomial monomial
basis to actual K0. Its value formula identifies every basis vector with
the actual induction monomial.

`segmentSpecialPolynomialEvaluation` substitutes the actual classes
`gradedSegmentSpecial` of the increasing special quotient.
`zelevinskyEndomorphism` composes this substitution with the inverse
polynomial comparison. It is the whole-ring endomorphism described in
Zelevinsky §9.12, printed p.201, constructed from the actual segment
classes. Its generator formula is proved. `ZelevinskyInvolutivityStatement`
is the separate precise target that this constructed endomorphism squares
to the identity on every class. From such a proof,
`zelevinskyRingInvolution` constructs the corresponding ring automorphism.
This preserves the source distinction between constructing the
endomorphism and proving involutivity.

The original proof of Corollary 7.5 uses the classification basis of §6.5
and the triangular unipotent multiplicity matrix of Theorem 7.1 on each
fixed cuspidal support. The involutivity proof uses Proposition 9.13 and
the alternating subdivision calculation in §9.14, printed pp.201–202.
These source inputs are not proved merely by the evaluation or basis
constructors. The actual segment classes additionally retain the
constituent-existence and Aubert dependencies documented in
`SegmentGrothendieck`. All these representation-theoretic obligations
are separate from an external Chapter V structural boundary.

This module constructs no equality with the support-adjusted Aubert
operator. That equality also needs the actual graded adjusted operator,
its multiplicativity and unit formulas, its segment exchange, and the
additive passage from monomials to all classes. The subsequent comparison
targets retain those obligations explicitly.
