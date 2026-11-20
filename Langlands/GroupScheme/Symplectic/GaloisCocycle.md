# Finite Galois cocycles of the split symplectic group scheme

`Langlands.GroupScheme.Symplectic.SplitSymplecticGaloisCocycleStatement` states that every cocycle of the actual standard symplectic group scheme on a finite Galois field cover is trivial on that cover. This is the split symplectic first cohomology calculation used in Kneser's *Lectures on Galois Cohomology of Classical Groups*, TIFR Lectures on Mathematics 47, 1969, §1.7, Example 3, and §5.8, printed p. 92 (PDF p. 98). [TIFR publication](https://mathweb.tifr.res.in/sites/default/files/publications/ln/tifr47.pdf)

The affine matrix comparison identifies the ambient unit-group points with the invertible matrices over the coefficient algebra and respects coefficient maps. Under this comparison, the represented symplectic subgroup consists of the matrices preserving the standard alternating matrix. Thus the Galois values of a scheme cocycle satisfy the split symplectic matrix cocycle identity.

The matrix theorem provides a symplectic primitive over the original extension field. The affine comparison lifts it to a point of the actual symplectic group scheme. The closed inclusion is a monomorphism, so the matrix coboundary identity implies the identity on scheme points. Galois values determine a cocycle on the entire finite Galois cover.
