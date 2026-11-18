# The two positive prefixes and the crossed quotient kernel

The original and flipped character presentations have the same outer mode
parities. On each outer pair, the flipped upper character changes the
reflection sign of the quotient tail. The double Fourier coefficients of
their images differ by the product of the two tail factors. On the high
input rectangle these factors are nonzero on the required parities. The
quotient section identity thus identifies the section's double coefficients
with those of the flipped input after multiplication by the two mode signs.
Off-parity coefficients vanish in both presentations.

The binomial at the inner crossing of the flipped presentation has only
low modes on the middle rotation. The two presentations have the same
middle parity, so the differential tail polynomial for the original
presentation kills these coefficients. For outer output modes at or above
the crossed cutoffs in absolute value, the input rectangle stays above the
original cutoffs and has fixed signs on both axes. Subtract the flipped
binomial image times the product of these signs from the original section.
The rectangle of the difference vanishes. Its middle polynomial image has
the coefficients of the original middle tail, so
`RealAdjacentFourierBand.rectangle` makes the high double output coefficient
zero.

The crossed quotient acts by the product of its two outer tails. This
product kills the double coefficients below either cutoff on the appropriate
parity classes. Outside those classes the input coefficients vanish. The
high coefficients vanish by the rectangular argument, since the crossed
cutoffs are the original cutoffs plus the middle polynomial degree. Finite
Fourier uniqueness on the outer rotations gives zero in the crossed
standard module. The inclusion into the crossed character presentation
preserves the underlying function, and the quotient is the actual
before-descent map applied to the original section.

The proved containment for the original prefix and the flipped containment
give `RealInducedPairPositivePrefixKernelStatement`. The derived equivalence
`absorption_iff_ker_eq` characterizes positive absorption as equality of this
sum with the crossed quotient kernel. The equality requires the remaining
inclusion of the kernel in the sum.
