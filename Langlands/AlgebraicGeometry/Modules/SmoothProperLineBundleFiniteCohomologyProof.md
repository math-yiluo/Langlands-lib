# Finite line-bundle cohomology from a perfect representative

`smoothProperLineBundleFiniteCohomology` proves the full proposition
`SmoothProperLineBundleFiniteCohomologyStatement`.

The proof specializes the existing additive-functor instance to the actual
field. It then uses the existing `universalPerfectSections` theorem over the
actual base field to obtain a bounded complex of finite projective modules
representing the actual derived sections of the given line bundle. The
published derived-category comparison identifies its homology in each
nonnegative degree with `DerivedSections.relativeCohomology f n`.

A cycle space is a subspace of the corresponding finite-dimensional term,
and homology is a quotient of cycles. The existing finite-homology lemma
therefore gives finite dimensionality, which the cohomology isomorphism
transports. Above the upper term bound, the complex term is zero, so its
homology and the actual sheaf cohomology are zero. Taking the natural part
of that upper integer bound plus one yields an eventual vanishing bound
for natural degrees, including when the integer bound is negative.

The universal base-change conclusion of the perfect-sections theorem and
the representative's lower bound are not needed here. No numerical degree
formula or further geometric finiteness assumption is introduced.

The corollary `smoothProperLineBundleTensorPowFiniteCohomology` packages each
actual nonnegative tensor power as a line bundle using the published
`Picard.tensorPow_isLocallyFreeRankOne` theorem, then applies the proved
finiteness theorem. It imposes no ampleness hypothesis, includes the zeroth
power, and supplies the finiteness family needed to discuss an Euler
polynomial.
