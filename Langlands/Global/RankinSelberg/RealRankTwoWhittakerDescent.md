# Ascending character descent for real rank two

`realRankTwoWhittakerDescent` identifies the exact Whittaker models of a real block list of total rank two and its ascending character expansion. The equality holds at every complex exponent and for every nonzero real additive parameter.

For two character blocks the expansion leaves the list unchanged. An induction block of weight zero has the same standard module as its two character positions. For a nonzero induction weight, the ascending Fourier multiplier surjects onto the induction block. Its kernel has only the rotation modes of absolute weight strictly less than the absolute induction weight. Those finitely many Fourier coefficients at the identity determine all coefficients on the orthogonal group, since every element is a rotation or a rotation followed by a reflection. The compact restriction determines the standard vector. Thus the kernel is finite dimensional, and `realWhittakerFiniteKernelDescent` gives the inclusion into the block model. Equality of exact and uniform coefficient spaces and the ascending quotient give the converse inclusion.

This comparison implements the passage between the real standard block model and a principal series used in Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 11.1. It treats the two-dimensional case by the Fourier description of the kernel.
