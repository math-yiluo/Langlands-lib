# Reversing actual rank-one norm-kernel cocharacters

This internal derived development uses the actual relative-root-system proof,
the integral character comparison modulo ambient characters, and split-torus
pairing detection. It introduces no external-source assertion.

`HasReversingNormalizer i zeta` means that an actual rational point normalizing
the supplied torus sends its integral cocharacter zeta to its negative under
the torus automorphism induced by conjugation.

Suppose every torus character has a positive integral multiple equal to a
restricted ambient rational character plus an integral multiple of alpha.
Suppose zeta annihilates every such ambient restriction and an actual relative
Weyl class sends alpha to its negative. Invariance of the lattice pairing makes
the reflected zeta pair with alpha by the negative original pairing and still
annihilate all ambient restrictions. Applying each character's integral
relation and cancelling its positive denominator shows the same negation for
every character. Split-torus pairing detection gives equality of integral
cocharacters.

For a connected reductive group over an arbitrary field, with an actual
maximal split torus and singleton actual simple-relative-root set, the
published structural theorems supply both the character relations and a
reflection in that root. A representative of its class in the actual quotient
of rational normalizers by rational centralizers gives the required rational
normalizer. The final theorem applies this to the integral Weyl correction
`normKernelCocharacter i nu`, which annihilates every ambient character.
The ambient group need not be split.

This is a cocharacter symmetry result. It does not assert positivity of an
adapted-line character, a height estimate, or adelic chamber coverage.
