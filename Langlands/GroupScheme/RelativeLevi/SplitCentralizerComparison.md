# Actual centralizers depend only on the zero-root face

This derived module compares actual cocharacter centralizers in one supplied
split maximal torus of a reductive group over a nontrivial commutative ring.
A supplied full fibrewise coordinate root datum is required. No noetherian,
reducedness, localness or connectedness assumption is placed on the ring.

The pairing lemma chooses any maximal-ideal field fibre to prove that the
supplied full coordinate pairing is the usual integer dot product. The generic
`Dynamic.centralizer_eq_top_of_isCentral` proves on every scheme test that a
central cocharacter has constant conjugation orbit.

`cocharacterInCentralizer` is the actual factorization of a second coordinate
cocharacter through the original cocharacter's relative centralizer, using their
common ambient torus. Its composite is the specified second ambient cocharacter.
If every original zero-pairing root also pairs to zero with the second
cocharacter, `isCentral_cocharacterInCentralizer` proves that this factored map
is central. The original centralizer is reductive, its original torus remains
fibrewise maximal, and its actual full fibrewise root datum is the orthogonal
restriction, by `RelativeCentralizerReductive` and `RelativeCentralizerRootDatum`.
The second cocharacter annihilates all those root characters. The published
arbitrary-ring full-centre criterion `mem_center_of_rootCharacters_one` therefore
proves centrality on every scheme test.

`centralizer_le_of_zero_imp` now proves inclusion of actual centralizer subgroup
functors: the original centralizer is in the centralizer of the factored central
map, and the actual ambient inclusion transports that membership. Thus agreement
of the two exact zero-root sets gives `centralizer_eq_of_zero_iff`. The definition
`centralizerIsoOfZeroIff` constructs the actual comparison isomorphism between
the two specified relative centralizers, and its companion theorem proves the
exact ambient inclusion equation.

Equality or an isomorphism of centralizers is a conclusion, not a supplied
premise. The torus and root datum are fixed throughout, and the nontrivial-ring
assumption is explicit. Comparison of parabolics, canonical filtration overlaps
across different tori, the empty-base case of the final statement, and global
descent remain separate steps of the finite vector-bundle filtrations of
supplied relative radicals.
