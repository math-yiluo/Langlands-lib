# Actual norm and depth witnesses for first-order assembly

Worker 84 implements the norm and depth helpers used by the final assembly.
A discrete valuation bound v(a)<=v(b), b nonzero, puts a/b in the actual supplied
integer ring. Its canonical norm is at most one, so multiplicativity gives the
corresponding canonical norm bound. The base-extending spectral norm of p^k is
exactly p^(-k), by its actual extension property and the ordinary p-adic formula.

For a nonzero intermediate coefficient b, the weighted total trace is a nonzero
base-linear functional: if it vanished, substituting b inverse times x would
make the ordinary trace zero, contradicting the finite-separable trace theorem.
This provides the separate detector needed for depth nontriviality even when
the fixing subgroup contains every automorphism.

Every integral y and positive k give a norm-one actual unit 1+p^k*y. The actual
canonical norm of p is less than one and the norm of y is at most one. The
ultrametric equality therefore gives norm one for the sum, hence nonzero field
value and its unit structure. No arbitrary chosen coordinate or extra norm-one
hypothesis is supplied by the consumer.

The carrier universes remain unrestricted and all primes including two are
retained. AuxiliaryCharacterFirstOrderProof combines these lemmas with the constructed
characters, nontrivial additive detectors and topology comparison to establish
the final depth and exact-stabilizer assertion.
