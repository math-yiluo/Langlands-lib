# Actual inverse-transpose images of cuspidal operator realizations

This internal helper for Task 7294 applies the established subrepresentation
transport construction to the inverse-transpose involution of the actual
stable automorphic core. The algebraic image construction follows
`OperatorCMTransport` and the general
`conjugatedSubrepresentationOrderIso`. It works over a number field in arbitrary
universe and retains all finite, compact and differential operators.

`continuousTranspose` has the same underlying actual function as the Library's
`ContinuousRationalFunctions.transposeDual`. The published
`isCuspidal_transposeDual` proves cuspidality through actual constant terms: a
rational block permutation exchanges the two block sizes and negative transpose
changes the matrix quotient variable, preserving normalized Haar measure.
The present file reuses that result. Involutivity proves reflection of cuspidality.

`OperatorRealization.transpose` is the actual linear image of the represented
subspace under `StableAutomorphicFunctions.transpose`. Whole-algebra covariance
makes the image invariant. The restricted linear equivalence has the expected
finite and compact covariance and enveloping covariance. The real Lie version
uses the generator of the enveloping algebra and complexification of negative
transpose. The inclusion and evaluation identities refer to the original actual
adelic functions.

Image and preimage give an order isomorphism on the invariant subspaces of the
restricted representations, so full-operator irreducibility is preserved and
reflected. The actual continuous-function identity and constant-term preservation
likewise preserve and reflect cuspidality. These facts define
`CuspidalOperatorRealization.transpose` and its vector equivalence with all three
operator covariance formulas.

This constructs the cuspidal transpose image. It leaves the identification as a
contragredient open; no invariant pairing or surjectivity onto contragredient
functionals is asserted here.
