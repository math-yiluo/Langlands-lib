# Galois coboundaries in split symplectic matrices

`Langlands.GroupScheme.SymplecticMatrix.SplitSymplecticGaloisCoboundaryStatement` states that a crossed cocycle of invertible matrices preserving the standard alternating matrix is a coboundary of a symplectic matrix on the same finite Galois extension. This is the matrix calculation for split symplectic groups in Kneser's *Lectures on Galois Cohomology of Classical Groups*, TIFR Lectures on Mathematics 47, 1969, §1.7, Example 3, applied in §5.8, printed p. 92 (PDF p. 98). [TIFR publication](https://mathweb.tifr.res.in/sites/default/files/publications/ln/tifr47.pdf)

Matrix Hilbert 90 first produces an invertible primitive. Since the cocycle preserves the standard alternating matrix, its pullback by the inverse primitive is Galois invariant. Its entries descend to the ground field. Invertibility, skew symmetry, and zero diagonal descend along the injective coefficient map.

Darboux normalization over the ground field gives an invertible matrix that carries the standard form to the descended form. This matrix is fixed by the coefficient automorphisms. Multiplying the primitive on the right by its scalar extension preserves the coboundary identity and makes the primitive symplectic.
