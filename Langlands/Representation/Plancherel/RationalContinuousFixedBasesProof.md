# Proof of continuous finite fixed matrices for actual rational induction

`RationalNormalized.rationalContinuousFixedBases` proves the unchanged
`RationalNormalized.RationalContinuousFixedBasesStatement`, with independent
field and representation-carrier universes. The family is the existing
`complexInduced` on the full complex unramified-character space for all
rational norm characters of the actual Levi.

The proof first derives closedness of the actual parabolic point subgroup
from the compatible root presentation. A nonarchimedean local field is
Hausdorff, so the rational-point image of the closed immersion is closed.
The displayed compactness of the literal left parabolic quotient is installed
as an instance.

The published `universalInduced_fixed_finite_free` then supplies finite
freeness of the universal compact-open fixed module over `RegularAlgebra r`.
Its hypotheses are discharged by continuity of the rational norm characters,
the displayed continuity of the actual Levi projection, admissibility of
the inducing representation, parabolic closedness and literal quotient
compactness. The proof transfers finite freeness to the scalar-restricted
complex fixed-vector carrier through
`CoefficientRestriction.complexFixedVectorsEquiv`. This equivalence retains
the original coefficient action on the same vectors.

`Module.finBasis` chooses a coefficient basis indexed by one `Fin d`.
For every character, `rationalNormalizedInducedSpecialization` proves
bijectivity of the canonical full-induced specialization. Applying
`inducedSpecializedBasis` gives the actual complex fixed-space bases with
that common finite index.
Finally `inducedSpecializedBasis_continuous` supplies the required continuity
of every actual normalized Hecke-compressed matrix entry: each is evaluation
of one regular coefficient independent of the character.

This is an internal composition of published results. It assumes neither
unitarity nor irreducibility. The proof allows zero-dimensional fixed spaces
and asserts no topology or continuity of the bases themselves. It concerns
positive full-parabolic normalization; comparison with the host's positive
Levi normalization, uniform detection of irreducible subquotients, nonzero
fibers and an irreducible parameter remain separate obligations.
