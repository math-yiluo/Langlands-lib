# The enveloping action on realized adelic block sections

`sectionEnvelopingAction` is the complex universal enveloping action on `smoothCompactFiniteSections`. Its real generators act by the infinitesimal right translations of `sectionDifferential`. On each fixed finite slice, every enveloping operator acts by the Library's smooth archimedean differential operator.

The proof checks real linearity on all slices, then extends the real differential complex linearly. On a pure tensor in the complexified Lie algebra, the resulting slice operator is a complex multiple of the real differential. Tensor induction identifies it with the smooth slice's complex Lie action. Since the slices determine the section, the bracket law follows from the smooth slice's bracket law. The universal property supplies the enveloping action, and induction on real generators proves its slice identity. Finite right translation shifts the finite argument and therefore commutes with every enveloping operator. Infinite compact right translation satisfies the adjoint covariance law by the corresponding identity on each smooth slice.

This is an internal construction of the differential operators for the smooth realized block model. Langlands (1979), proof of Proposition 2, pp. 204–205 (PDF 199–200), describes the smooth compact-finite scalar sections with cuspidal Levi slices.
