# Actual prime extraction from Harris local frame coordinates

This internal unit specializes `localFrameToPrime` to the underlying actual
adelic frame of a compatible Harris Weil frame, with the regular rational module
`A`. It retains the original datum, signature charts, geometric prerequisites,
field-valued point and positive polarized action object.

`localFramePrimeMap` is the resulting rational linear map from the completion at
a finite place tensor `A` to the actual rational Tate module at the prime selected
by `primesEquiv`. `localFramePrimeMap_coordinate` applies the generic inverse-frame
factorization. The tensor map in that result agrees definitionally with the
coefficient-change algebra map in `localFrameCoordinate`, so evaluated Harris
coordinates recover the actual prime coordinate.

`rationalFullToPrime_eq_of_localFrameCoordinate_eq` applies that linear map to an
equality of local coordinates and rewrites both sides by the factorization.
`rationalFullToPrime_fixed_of_levelIso_fixed` uses the existing fixed-coordinate
witness from local smallness and the explicit finite-order premise on the actual
rational self-isogeny. It concludes that actual prime extraction of each full
rational Tate section is fixed by the self-isogeny.

The finite-order premise remains essential. This unit does not establish
surjectivity of prime extraction, its naturality for rational homomorphisms,
one-prime faithfulness, positivity, finite order, or the exact CM small-level
rigidity theorem. It is derived solely from the imported actual constructions
and their proved identities; no external literature claim is added.
