# Injectivity of the diagonal projection for complex matrix products

`diagonalCenterPolynomialEquiv` identifies the centre of the enveloping algebra of a finite product of complex matrix Lie algebras with its image in the diagonal polynomial algebra. The proof extends the PBW and symbol argument of `VermaCentral.gamC_injective` in `LowerVermaCentral.lean` to matrix products.

Suppose a central element has zero diagonal polynomial. Its membership in the strict upper right ideal forces each nonzero PBW coordinate to have a strict upper letter. Each such monomial has total adjoint weight zero by centrality, so it also has a strict lower letter. The highest nonzero degree symbol vanishes on upper triangular tuples. It is killed by the coadjoint derivations of all the matrix units, since commutators with the original central element vanish. Its zero set is stable under conjugation at each matrix place. Triangularizing each matrix over the complex numbers shows the symbol vanishes everywhere, contradicting its highest nonzero PBW coefficient.

This is a derived algebraic comparison for the Levi centre finiteness in Langlands, *On the notion of an automorphic representation* (1979), Lemma 4, printed p. 204. The construction uses the Library's PBW basis, coadjoint invariance of zero sets and complex triangularization.
