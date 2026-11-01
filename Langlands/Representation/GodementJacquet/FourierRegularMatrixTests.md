# Matrix tests with regular support on both Fourier sides

This is an internal auxiliary construction for the supercuspidal matrix
functional-equation proof. It works in every square rank over a Hausdorff,
locally compact, totally disconnected topological field with Borel measurable
space. The scalar additive character and its supplied self-dual additive Haar
measure are retained.

`regularMatrixTests d` is the complex subspace of full-matrix Schwartz–Bruhat
functions that vanish on all noninvertible matrices. Its functions restrict
to genuine Schwartz–Bruhat functions on the actual general linear group via
`regularMatrixTestRestriction`. The compact-support assertion is in the
group's topology: the proof uses closed nonvanishing support of locally
constant functions and the topological embedding of GL into the matrix space.

`fourierRegularMatrixTests d ψ ν hsd` is the intersection of this subspace
with its inverse image under `rectangularFourierEquiv ψ ν d d hsd`.
Consequently both the test and its actual Fourier transform vanish on singular
matrices and have compact support on GL. The Fourier transform is the full
plus-sign entry-pairing integral against the nested square product of the
supplied scalar measure.

The two stability lemmas use the published Fourier square-reflection formula
and inverse evaluation formula. Negation preserves singular matrices; the
original test therefore provides the second support condition after another
Fourier transform. This proof does not assume a separate Fourier closure
premise.

The motivation is Godement and Jacquet, *Zeta Functions of Simple Algebras*
(1972), registered source `godement-jacquet-1972-zeta-simple-algebras`,
Lemma 5.3, printed pages 59–61 (one-based PDF pages 69–71). The retained
original is
`/home/taskhub/central-library/Godement-Jacquet--Zeta functions of simple algebras (book)--1972.pdf`,
SHA256 `86a8900900504adeb5757a04b5bb8a8754e6ef00b0fff49754096d371f59d568`.
That source defines a space using singular vanishing and proper parabolic
unipotent averages, and proves its Fourier stability. The present auxiliary
space records the resulting two support conditions directly. No equivalence
with the source's space, vanishing of parabolic averages, nonzero test,
operator realization, or functional equation is asserted in this module.
Constructing sufficiently many such tests from the representation remains a
separate proof obligation.
