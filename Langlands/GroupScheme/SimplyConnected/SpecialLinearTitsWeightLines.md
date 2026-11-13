# Coordinate lines preserved by inner Tits discrepancies

Author: Worker 239.

This internal unit supplies an all-test matrix consequence of an actual local
special-linear presentation `E`, a torus homomorphism into its target, and
characters `χ` giving the local diagonal coordinates of that torus on every
test and at every cover point. No presentation or characters are constructed
here.

An inner discrepancy fixes each such coordinate matrix, since its associated
point of the target is independent of the cover point. Thus its representing
matrix commutes with the diagonal torus after the coefficient map.

To detect its entries over the cover field `L`, `laurentCoverPoint` uses the
canonical map from `Spec L[T,T⁻¹]` to `Spec L`. Its coefficient map gives
constant Laurent polynomials. `genericTorusPoint` follows the generic Laurent
unit by a supplied cocharacter `ν` of the torus. Evaluating a character `χ i`
at this point gives the monomial whose exponent is its actual lattice pairing
with `ν`; the proof uses the published identification of endomorphisms of
`Gm` with integer power maps.

`HasInnerDiscrepancy.entry_eq_zero_of_weight_ne` evaluates the diagonal
commutation identity on this generic test and compares the two resulting
Laurent monomials. If the integer weights differ, their common coefficient,
the matrix entry, must vanish. In particular a coordinate whose weight is
different from every other weight has its coordinate line preserved, as
`HasInnerDiscrepancy.preservesCoordinate` proves.

For actual Tits data and characters whose adjacent differences are the numbered
simple-root restrictions, the endpoint-weight results apply with the actual
positive cocharacter. `preserves_first` and `preserves_last` give the respective
coordinate lines when the corresponding end vertex is distinguished.
`exists_normalized_inner_cocycle` then turns a supplied family of inner
representatives on any automorphism subgroup into a family with the same
all-test discrepancies, the identity and honest semilinear cocycle laws, and
the first coordinate vector fixed. The construction uses the first-line
normalization; it requires `n > 0` and the distinguished first vertex.

The argument works in arbitrary characteristic, including finite cover
fields, because it uses the generic unit rather than just field-valued torus
points. It does not assert the existence of an inner discrepancy, a separated
weight, or a Hermitian presentation. The normalized cocycle conclusion requires
the explicitly supplied inner representatives and the actual endpoint hypotheses.
