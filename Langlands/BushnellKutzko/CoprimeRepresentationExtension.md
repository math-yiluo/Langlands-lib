# Extending an irreducible representation by a scalar correction

`coprimeRepresentationExtension` proves `CoprimeRepresentationExtensionStatement`,
the coprime-index step used in the proof of Bushnell–Kutzko (1993), (5.2.4),
printed pp. 167–168 (PDF pp. 179–180). The retained source
`bushnell-kutzko-1993-admissible-dual-gln` has SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The group of conjugating operators is the normalizer of the graph of
`η` in `G × Aut_ℂ(W)`. Its projection onto `G` is surjective by the
conjugation invariance hypothesis. Schur's lemma identifies the kernel
with the central complex scalars. The supplied representation of `P`
splits the projection over `P`. The difference between a conjugating
operator over `P` and the supplied operator is a unique scalar. This
scalar defines a character of the preimage of `P`, and that character
is trivial on the graph of `η`.

The transfer of this character to the whole normalizer restricts on
the scalars to the power given by the index of `P`. The determinant
of a conjugating operator raised to the supplied exponent restricts
on the scalars to the power given by the degree times that exponent.
Both characters kill the graph of `η`. Bézout's identity gives a
character of the normalizer that is the identity on the scalars and
still kills the graph. Dividing each conjugating operator by this
character yields a representation that descends to `G` and agrees
with `η` on `N`.
