# Relative étale Künneth isomorphisms for abelian schemes

`Langlands.Cohomology.AbelianRelativeEtale.RelativeEtaleKunnethStatement`
asserts the cohomological Künneth isomorphism for the fibre product of
abelian schemes over a quasi-compact scheme `S`. The coefficient is the
constant regular module for `R = ℤ/p^rℤ`, where `p` is prime and
invertible on `S`. The scheme and sheaf-module carriers have universe
zero. The localizations for the base and the total schemes have
independent universes, with a common choice of size for all total schemes.

The target is the actual higher direct image of the constant coefficient
sheaf on the binary product in `Over S`. The source is the finite
biproduct over `i : Fin (q+1)` of the tensors of the actual higher direct
images in degrees `i` and `q-i`. The sheaf tensor product is obtained by
sheafifying the pointwise tensor product over `R`.
The proposition chooses one family of isomorphisms for all pairs of
abelian schemes in degree `q`. Naturality is the square for the actual
relative pullbacks along morphisms of the factors over `S` and their
product. This includes multiplication in either factor. These conditions
are satisfied by the canonical external cup-product isomorphism of the
source theorem. The proposition expresses natural existence.

Milne, *Étale Cohomology* (1980), VI §8, Theorem 8.5, printed pp. 258–259,
gives the cohomological Künneth isomorphism under flatness of the first
sheaf and its higher compact-support images. The book assumes locally
Noetherian schemes in its Terminology and Conventions, printed p. xiii.
To obtain the statement over `S`, form the relative external cup-product
map of higher direct images. At each geometric point with algebraically
closed residue field, proper base change for both factors and their
product identifies the stalk map with the external cup-product map over
that field. Stalks commute with the finite biproduct and the sheaf
tensors in the source. This uses SGA 4, tome 3, XII, Corollary 5.2(iii),
printed p. 89 (PDF p. 92).

Over the field, properness identifies the compact-support and ordinary
higher direct images. The constant regular module is flat. The proper
geometric abelian varieties have finite cohomology with finite constant
coefficients in every degree and at every exponent by SGA 4, tome 3,
XIV, Corollary 1.2, printed p. 145 (PDF p. 148). This finiteness and the
flatness of the constant coefficient stages give the hypotheses of the
reduction sequence in Milne 1980, V.1, Lemma 1.11, printed pp. 165–166.
Milne, *Abelian Varieties*, §15, Theorem 15.1(b), gives integral freeness
in each degree. Freeness in the next degree makes the torsion term in
the reduction sequence zero. Consequently each higher image over the
field is free over `R`. At `r = 0` all the modules are zero. Theorem 8.5
now gives an isomorphism on every geometric stalk, which implies the
claimed isomorphism on the small étale site of `S`.

The external cup-product map pulls back classes along the two
projections and takes their cup product. Functoriality of these
operations gives the pullback squares in the statement. Iteration on
abelian powers gives the relative decomposition used in
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p. 98 (PDF p. 106). Passage through the
coefficient reductions and identification with the rational adic
projector are additional comparisons.

The source fingerprints are as follows.

| Edition | Registered ID | SHA-256 |
| --- | --- | --- |
| Milne, *Étale Cohomology* (1980) | `milne-1980-etale-cohomology` | `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232` |
| SGA 4, tome 3 (1973) | `sga4-1973-tome3-deligne-xvii-original-scan` | `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a` |
| Milne, *Abelian Varieties*, author revision of 2 January 2022 | `milne-abelian-varieties-1986-author-2022` | `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c` |
| Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties* (2001) | `harris-taylor-2001-geometry-cohomology-simple-shimura` | `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b` |
