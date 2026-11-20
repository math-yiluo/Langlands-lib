# Fourier transformation of slices and marginals

Let `E`, `U` and `L` be finite-dimensional real inner product spaces with their Borel measures and inner-product Lebesgue volumes. Let `Φ` be a complex-valued Schwartz function on their Hilbert product. Set the `U` frequency of its Fourier transform to zero and integrate over the `L` frequency. The result is the Fourier transform on `E` of the function obtained by setting the physical `L` coordinate of `Φ` to zero and integrating over `U`.

Lean first proves the Fourier–marginal identity on a two-factor Hilbert product. The Fourier kernel at second coordinate zero depends only on the first coordinate. The Hilbert product volume is the product of the coordinate volumes, so the identity follows from Fubini, with absolute integrability supplied by the norm-one Fourier character. Applying Fourier inversion gives the identity with integration on the Fourier side. An inner-product preserving coordinate permutation lets Lean apply both identities to the three-factor product.

For complex square matrices the three factors will be the diagonal, strictly upper entries and strictly lower entries. The identity is used to compare the two diagonal tests in Jacquet's matrix-coefficient zeta integral.

Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, equations (4.3) and (4.4), pp. 30–31.
