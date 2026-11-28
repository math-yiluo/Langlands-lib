# Regular orbital-integral transfer from division units to the general linear group

`divisionRegularTransfer.{u}` proves `DivisionRegularTransferStatement.{u}`.
The dimension hypothesis identifies the matrix size with the reduced degree of the
division algebra. For the supplied Haar measures, the ordinary regular orbital
charts and the division orbital profile give compatible centralizer and quotient
measures. Each centralizer measure gives its largest compact open subgroup mass one.

The normalized orbital integrals of the division test descend to a Schwartz–Bruhat
function `P` of the reduced characteristic coefficients. Every point of its support
is a regular elliptic characteristic coefficient vector on the split group. The
ordinary orbital-profile realization theorem gives a Schwartz–Bruhat function on
the split group with normalized profile `P`. Multiply it by the characteristic
function of the inverse image of the support of `P` under the split characteristic
coefficient map. This inverse image is clopen. The product is locally constant and
has compact support in the regular elliptic locus. The cutoff is constant on each
conjugacy class and preserves the profile `P`.

At corresponding elements, equality of their coefficients identifies their
normalized orbital integrals. A supplied topological group isomorphism between the
centralizers transports their largest-compact-open-subgroup normalization. By Haar
uniqueness, any associated pair of centralizer measures therefore differs from the
normalized pair by the same positive scalar. Compatibility rescales both quotient
measures inversely, so equality persists for all the measures in `MatchAt`. The
regular elliptic support gives vanishing at regular nonelliptic elements.

This proves the regular-support division-unit specialization of the orbital-integral
assertion in Deligne–Kazhdan–Vignéras (1984), B.2.c 1), printed p. 83,
`bdkv-1984-representations-local-field`
(SHA-256 `c1a4b4bd79575b5b41c15e1dacaf9a8094bd05c189efed06e27c62a64d22fcc3`).
Badulescu (2002), §5 and §6, printed pp. 733 and 745–746, gives regular-support
matching by submersion and describes the polynomial correspondence.
Source
`badulescu-2002-jl-char-p` (registered folder SHA-256
`dc96cc7848166e83a1f23478a1e341928ea8565bc9b649ffe84e452f3a205028`, published PDF
SHA-256 `638e7134bb13c9c718ee7e5c2c9f06634637598c6ba8cd465345baf1234ed370`).
