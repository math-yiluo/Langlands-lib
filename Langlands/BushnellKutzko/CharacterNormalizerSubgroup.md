# Character normalizers and intertwining sets

`characterNormalizerSubgroup` bundles the existing `characterNormalizer`
set of a character of a subgroup `H`. Its elements preserve `H` and the
character values. Composition composes the conjugations on `H` and
preserves the two conditions. Inversion evaluates the original
conjugation formula at the inverse conjugate.

The two `mem_characterSelfIntertwining_mul` lemmas show that the
self-intertwining set is stable under left and right multiplication by
any element of this normalizer. In each case the intermediate conjugate
belongs to `H` by the domain-normalizing condition, so the intertwining
identities compose. Multiplication by the inverse gives the converse.

`characterNormalizer_eq_mul_of_doubleCoset` is the group calculation
used in the proof of the simple-character normalizer. Suppose the
intertwining set is `Y B Y` for subgroups `Y` and `B`, with `Y` in the
character normalizer. If the domain-normalizing subgroup of `B` normalizes
`Y`, the character normalizer is the product of `Y` and that subgroup.
The proof strips the two outer factors from a normalizing element,
then moves the right outer factor across the middle. For the reverse
inclusion, all elements of `B` intertwine the character because the
outer subgroup contains the identity.

The definition of intertwining and the source of the double-coset
calculation are Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), source ID `bushnell-kutzko-1993-admissible-dual-gln`,
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
§3.3, printed p. 104 (PDF p. 116), and (3.3.17), printed p. 112
(PDF p. 124).
