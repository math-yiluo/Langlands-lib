# Actual mixed line-bundle Euler coefficients

This internal interface expresses the mixed degree needed for the Rosati trace formula in terms of the Library's actual coherent cohomology. It introduces no arbitrary intersection pairing or supplied positive form.

For a proper scheme over a field and actual line bundles `L` and `N`, `mixedLineBundleEulerPolynomial f L N d` is the coherent Euler polynomial of `N` twisted by natural powers of `L`, minus the Euler polynomial of the structure sheaf twisted by those powers. Under a dimension bound it therefore evaluates to

`χ(N ⊗ L^n) − χ(L^n)`.

The truncation parameter is explicit. `mixedLineBundleEulerCoefficient` is its coefficient at index `d − 1`. This is a total definition: in dimension zero that index is zero. No geometric positivity in dimension zero is asserted by this definition.

The implemented proofs show that a trivial coefficient bundle gives zero, that actual coefficient-bundle isomorphisms preserve the polynomial, and that its natural evaluations agree with the difference of actual coherent Euler sequences. For `N = L`, the shift identity for coherent Euler sequences identifies the polynomial with the unit translation difference of the pure Euler polynomial. The published rational polynomial difference theorem then gives

`mixedCoefficient(L, L, d + 1) = (d + 1) * pureCoefficient(L, d + 1)`.

Finally, `lineBundleEulerPolynomial_topCoeff_pos` applies to a proper scheme over a field with `SmoothOfRelativeDimension g f` and `GeometricallyConnected f`, and requires an ample line bundle `L` (`hL : L.IsAmple`). Its proof identifies the canonical Euler polynomial with the polynomial in the published smooth proper line-bundle Euler theorem by equality of all natural evaluations. The ample branch of that theorem supplies exact degree and positive leading coefficient, giving positivity of the coefficient at relative dimension `g`. This includes dimension zero.

The provenance of the definitions and lemmas is internal, using actual coherent Euler polynomials and elementary polynomial operations. The geometric motivation is Milne, *Abelian Varieties*, author revision January 2, 2022, §17 Theorem 17.3, pp.35–36, registered source `milne-abelian-varieties-1986-author-2022`. In the usual positive-dimensional intersection notation, Riemann–Roch identifies this difference coefficient with `(L^(g−1) · N)/(g−1)!`; the pure top coefficient is `L^g/g!`. Thus twice their ratio has the normalization `2g (L^(g−1) · N)/L^g` in Milne's formula. These Riemann–Roch and trace comparisons, and positivity for a nonzero endomorphism's pullback of `L`, are motivation and remaining obligations; they are not proved or assumed by this module.
