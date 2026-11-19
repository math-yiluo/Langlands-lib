# The invertible middle polynomial in the flipped positive presentation

For two linked induction blocks of positive absolute weights `L` and `M`
and positive signed inner weight `H`, `RealInducedPairPositiveGenericMiddleStatement`
concerns the actual positive crossed quotient. In the four-character
presentation with the first pair's parities flipped, the chosen section of
a vector in the quotient kernel is the sum of two vectors `f₀` and `f₂`.
After the middle polynomial map, `f₀` has zero outer modes at `|i| ≥ L+H`
on axis 0 and `f₂` has zero outer modes at `|j| ≥ M+H` on axis 2.

The result is derived from the actual Frobenius and Fourier maps. On this
presentation, the middle parity is congruent to `H` modulo two. The
differential tail polynomial `P_H` is nonzero on all those integer modes
and has the symmetry sign of the generic swap. The two Frobenius maps
for `P_H` and its reciprocal are inverse by Fourier uniqueness. The
swapped list is the crossed four-character list with both parities of
its first pair flipped. Lean checks this by the crossed endpoint and
weight identities.

In any two-pair presentation, the double outer Fourier coefficient of
the quotient multiplies the input coefficient by the two tail factors.
The factors vanish below the cutoffs on admissible parities. Modes of
the other parities vanish in the input. On the two high windows the
admissible factors are nonzero. Flipping a pair preserves its mode
parity and multiplies its tail by the sign that is `1` at nonnegative
modes and `-1` at negative modes. This gives the comparison of quotient
maps on any two choices of endpoint parities and the agreement up to
one such sign for the original and first-pair-flipped sections.

If the actual crossed quotient kills the vector, the original middle
image, included into the original crossed presentation, has zero
double coefficients at both crossed high cutoffs. The original and
flipped middle maps have the same polynomial Fourier law. For a high
crossed double frequency the rectangular band lies within the original
high windows and keeps the sign of each frequency. The difference of
the two sections after multiplication by the constant sign on that
rectangle therefore gives zero at that output frequency. This proves
the same high-region vanishing for the flipped middle image.

The crossed quotient in the flipped presentation consequently kills
that image. Its kernel is the sum of the left and right binomial
images, each low in its own outer axis. Applying the inverse middle map
to the two terms gives the asserted decomposition of the section.
