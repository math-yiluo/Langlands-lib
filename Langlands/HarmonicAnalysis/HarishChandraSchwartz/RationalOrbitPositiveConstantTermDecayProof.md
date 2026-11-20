# Positive constant-term decay on the actual induced orbit

`rationalOrbitPositiveConstantTermDecay` proves the published
`RationalOrbitPositiveConstantTermDecayStatement` with independent field
and representation universes and every original standard index. For each
smooth section and each positive chamber parameter, the decay constants
are uniform over the whole unitary orbit and the full closed region.
The estimate uses the actual positive constant term, the original Levi Xi
factor, and the given positive-definite real cocharacter seminorm. The central quotient
Borel instance is bound inside the target proposition.

The proof obtains `RationalXiUpperBoundStatement` by applying
`rationalXiUpperBound_of_jacquetUnipotent` to
`rationalMinimalInducedJacquetUnipotent`. The latter uses the finite
geometric-lemma filtration of each normalized Jacquet module of the
minimal principal series. Every central point acts trivially on each
graded piece, which gives a uniform unipotence order. The Xi reduction
uses that order in the dominant lattice coefficient bound and specializes
to translates of the spherical vector and functional.

The proof of `rationalOrbitConstantTermThreshold` obtains a common
Casselman depth from fixed-vector dimensions for the original unramified
twists. Compact transport extends the identity to the full closed
minimal-Levi threshold region, and comparison with the same dynamic
constant term identifies the result with the original chosen constant
term. This supplies the threshold input for the same orbit and indices.

`rationalOrbitPositiveDecay_of_xiUpperBound_and_threshold` applies the
threshold to the original coefficient bound and compares Xi on the
closed chamber to derive polynomial growth. The Xi upper bound also
gives strict contraction of the nonunitary Jacquet exponents at a
compatible component point. The reduction combines uniform annihilators
with the weighted compact constant-term bounds and uses the split
positive-part decay theorem to obtain the conclusion.

The original result is Waldspurger's Lemma VI.2.3, printed pp. 299–301,
in *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), registered as `waldspurger-2003-plancherel`.
[Waldspurger 2003](https://doi.org/10.1017/S1474748003000082)
