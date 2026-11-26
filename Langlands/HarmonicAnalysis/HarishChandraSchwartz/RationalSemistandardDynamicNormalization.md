# Intrinsic quotient Haar in the dynamic Levi normalization

`CocharacterPresentation.leviNormalization` gives the inducing data used
in the actual V.3 comparison, starting with an irreducible admissible
representation of a literal semistandard Levi that is square integrable
modulo its split center. The input Haar measure is on the quotient of the
literal Levi by the point image of a split component of a closed model.
The construction works over any nonarchimedean local field and in
independent field and representation-carrier universes.

The point isomorphism for the cocharacter presentation identifies its
dynamic Levi with the literal Levi. The inverse image of the split center
is the point image of the split component obtained by transporting the
original one along the two Levi schemes' isomorphism. The quotient
isomorphism pulls back the input Haar measure and the square-integrability
condition. The inverse image of the split center is closed, and
unimodularity of the Levi gives invariance of the quotient measure under
right translations and inversion.

`CocharacterPresentation.leviNormalization_matches` shows that the
quotient isomorphism pushes the resulting measure forward to precisely the
input measure. In particular, the normalization has the source scale when
the given measure has mass one on the image of the compact Levi trace,
using `normalizedQuotientHaar_map_iff`.

This transport combines Waldspurger's Haar normalization in I.1 with the
split-central quotient used for square integrability and Schur
orthogonality in III.1. The resulting data serve the coefficient and form
comparison in V.3.1–V.3.2. The Lean proof uses the common inclusion of the
two Levi models into the ambient group.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, 2003, printed pp. 240, 264–265 and 294–295.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
