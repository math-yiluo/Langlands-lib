# The Appendix L-product from actual mixed segment pairs

Author: Worker 1765.

This internal adapter combines the centered-segment analytic product with the
actual finite Euler functions of the chosen midpoint bases. The
segment-head L-factor formula and the equal-rank supercuspidal L-factor
formula remain explicit premises. Whole-product multiplicativity is supplied
as an exact product of certified pair polynomials.

`centeredSegmentBaseEulerFamily_certified` eliminates the two positive-rank
notation transports to recover a certificate for the original midpoint
bases, with the actual smooth dual in the second variable.

`IsCenteredSegmentFamilyLProduct` records equality of a polynomial's
spectral reciprocal with the Appendix `blockLFactor` for the supplied
segment lengths minus one, real exponents and complex base functions.
It alone does not assert a representation certificate.

`reciprocal_of_centeredSegment_mixedPair` concerns the actual twist of
`δ i` paired with the actual smooth dual of the twist of `δ j`.
The functional-preserving twist-dual equivalence puts the latter action
in the form of exponent `-s j` on `(δ j).contragredient`.
The actual dual parameter constructor then supplies its strong head and
its actual smooth-dual midpoint base. The centered product formula gives
shift `(len i + len j - 2)/2 - k + s i - s j`. The positive lengths
convert the finite index set to
`range (min (len i - 1) (len j - 1) + 1)`, and the same shifts become
the Appendix `blockShift`. Euler certificate uniqueness identifies each
spectral reciprocal with the actual finite Euler function.

`centeredSegmentFamilyLProduct_of_certifiedProduct` evaluates the supplied
exact polynomial product, distributes complex inverse over its finite
products and applies the mixed-pair identity. These are pointwise
identities with totalized complex inverse, including at denominator zeros.
Meromorphic orders are not inferred from values at those zeros. The
canonical p-adic topology, additive character, self-dual Haar measure,
original actions, chosen midpoint bases and rank transports are retained.
