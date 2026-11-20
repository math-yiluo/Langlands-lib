# Finite induced support of a cuspidal isobaric sum

`cuspidalIsobaricSum_finiteSupport` proves the finite-place conjunct of the
induced-constituent property. The Lean proof chooses the local isobaric sums
and embeddings from the hypothesis. It applies `IsIsobaricSum.isSubquotient_normalizedProduct`
to the block shape with the supplied ranks in index order.

The exceptional set is the union of the exceptional sets of the cuspidal
presentations. At a place outside this union, `CuspidalSpectralPresentation.hasSpectrum`
supplies the spherical fixed-space condition for every inducing block. The
lemma `isSpherical_of_isIsobaricSum` applies that condition to the chosen local
isobaric sum.

This is the finite part of J. R. Getz and H. Hahn, *An Introduction to
Automorphic Representations* (2024), Theorem 10.7.5 and its proof, p. 288
(registered PDF p. 300). The local subquotient and spherical steps correspond
to Theorems 10.6.4 and 10.6.3, pp. 286 and 285 (PDF pp. 298 and 297).
The local occurrence lemma uses M. Tadić, *Classification of unitary
representations in irreducible representations of general linear group
(non-Archimedean case)* (1986), Proposition A.4(ii), p. 372 (PDF p. 39).
