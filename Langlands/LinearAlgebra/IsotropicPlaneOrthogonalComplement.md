# Isotropic vectors after removing a hyperbolic plane

`IsotropicPlaneOrthogonalComplementStatement` considers a symmetric bilinear form over a field, together with a normalized hyperbolic pair and two independent mutually orthogonal isotropic vectors. The hyperbolic pair's orthogonal complement contains a nonzero isotropic vector.

The proof assumes the complement is anisotropic. Any isotropic vector orthogonal to the first hyperbolic basis vector must then lie on that basis line, by the hyperbolic splitting. The totally isotropic plane contains a nonzero vector orthogonal to the first hyperbolic basis vector and must therefore contain the basis line. All its vectors are now orthogonal to that line and hence lie in it, contradicting their independence.

This is a derived linear algebra step for the binary block chosen in Springer's appendix to Kneser's *Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(ii), printed pp. 110–112 (PDF pp. 116–118). The lemma itself uses only the symmetric pairing and the specified isotropic vectors.
