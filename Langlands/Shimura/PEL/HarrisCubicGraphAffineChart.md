# Affine section embeddings for the canonical cubic bundle

For an ordinary polarized datum of positive degree index over a locally
noetherian scheme, the direct image of the canonical cubic bundle is locally
free of rank \(6^g d\). Its affine frame opens cover the base.
`Datum.AffineCubicFrame.toBase` gives each such inclusion from the spectrum of
the open's coordinate ring, which is noetherian.

`Datum.cubicGraphAffineChart` uses the closed immersion given by the local
evaluation of the cubic frame. After identifying the affine open with its
spectrum, this evaluation is the actual linear system in polynomial projective
space. Pulling back the coordinate presentation of the degree-one twist
gives the closed immersion by sections on the base-changed abelian scheme.
The linear-system twist isomorphism and base change of the canonical cubic
identify that same invertible module with the actual cubic bundle of the
base-changed datum.

The construction derives the inputs for the affine Hilbert-piece construction
from cubic direct image, the relative cubic embedding and the projective
coordinate presentation. The comparison retains the canonical cubic itself,
so graph section degrees use its original exponent.
