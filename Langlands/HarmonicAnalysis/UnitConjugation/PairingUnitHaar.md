# Unimodularity of the unit group from an invariant pairing

Let \(A\) be a finite-dimensional algebra with its module topology
over a nonarchimedean local field. Suppose \(A\) has a symmetric
nondegenerate pairing invariant under unit conjugation.
`pairingUnitHaarUnimodularity` proves that every left Haar measure
on \(A^\times\) is also right invariant.

## Proof

The additive Haar measure in the unit chart is preserved by
conjugation, by `pairingHaarPreservation`. The density
`unitHaarDensity` that converts this chart measure to left Haar
is the inverse left-multiplication modulus. That modulus is a
multiplicative character, so conjugation preserves the density as well.
The resulting group Haar measure is therefore invariant under
conjugation. Right multiplication by \(g\) is the composition of
left multiplication by \(g\) with conjugation by \(g^{-1}\).
It preserves the constructed measure, and Haar uniqueness transports
right invariance to the supplied left Haar measure.

## Source

The invariant pairing is the one used in Harish-Chandra,
*Admissible invariant distributions on reductive p-adic groups*,
University Lecture Series 16, 1999, Introduction, p. 2.
The argument derives unimodularity from the additive chart and
the two Haar-preservation facts. It applies to the idempotent
Levi of an algebra with an invariant pairing by
`invariantPairing_centralizer`, as needed for compatible Levi
quotient integration in parabolic descent.
