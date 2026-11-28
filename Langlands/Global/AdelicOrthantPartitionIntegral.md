# Regularized integration over a partition into translated faces

`RegularizedOrthantPartitionIntegralStatement` starts with a translated negative
orthant in finitely many real coordinates. Each cell has a compact base in the
coordinates complementary to its face and a continuous placement of this base
in the ambient space. The placement preserves the complementary coordinates.
In the face coordinates the cell extends strictly below the placed base. A
finite disjoint cover by such cells gives a sum formula for the regularized
integral of an exponential times a fixed polynomial. The formula uses
Lebesgue measure in the complementary coordinates, restricted to each base.
It holds wherever every ambient spectral coordinate is nonzero.

For the ordinary identity, positive real parts of the spectral coordinates
ensure absolute integrability on the translated orthant. Translation and the
finite monomial expansion reduce this to the product of the one-variable
integrability estimates `integrableOn_Iic_pow_mul_cexp`.

The cell chart first translates the face coordinates by a vector depending on
the complementary coordinates. It then recombines the two lists of
coordinates. Product Lebesgue measure is preserved by the translation in
each fibre and by the coordinate recombination. The chart's inverse image of
the cell is the product of its base with the strict negative orthant on the
face. Fubini gives the iterated integral. The strict and closed versions of
the face orthant agree almost everywhere since each coordinate hyperplane is
null. Finite additivity gives the ordinary identity on the positive-real-parts
chamber. `regularizedAffineFaceRecombination` then gives the stated identity.

This implements the integration step after a partition of the form (7.26) in
Delorme. The premises specify the partition and the complementary coordinate
measure. For the adelic application, the geometry of the relative coroot
spaces supplies the cells, and the parabolic quotient disintegration supplies
the comparison with the ambient and intrinsic Haar measures.

Source. P. Delorme, *On the spectral theorem of Langlands*, Advances in
Mathematics 426 (2023), 109107, §7, journal pp. 24–25 and 30, especially
(7.8)–(7.12) and (7.26).
