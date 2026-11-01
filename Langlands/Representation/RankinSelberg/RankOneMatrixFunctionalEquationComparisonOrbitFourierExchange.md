# Unipotent orbit Fourier exchange

This internal prerequisite integrates the actual bilinear rectangular Fourier
exchange over the actual upper-unipotent Haar measure. It uses the plus entry
pairing, the same supplied self-dual scalar Haar measure on both sides, and the
unsigned long Weyl matrix. It does not assert the gamma equation.

For two matrix Schwartz tests `Φ, Ψ`, write hats for their full rectangular
Fourier integrals, `χ` for the standard unipotent character, and `w` for the
unsigned long Weyl matrix. The two kernels are

* `χ(u)⁻¹ Φhat(iota(u) w X) Ψ(X)`;
* `χ(u)⁻¹ Φ(X) Ψhat(w u⁻¹ X)`.

The exchange theorem assumes that the topological support of `Φ` lies in the
invertible matrix locus, and that `Ψ` is supported in an actual comparison box
of positive principal-congruence level. It proves absolute integrability of
both kernels on unipotent times full matrices and equality of their product
integrals. All natural `n`, including zero, are allowed; the matrix size is
`n + 1`. The character is arbitrary and the scalar Haar measure is any supplied
self-dual one.

The Fourier-side convergence proof bundles the Fourier transform as an actual
Schwartz test by the published full rectangular Fourier equivalence. Reflection
`u ↦ w iota(u) w` changes the inverse-transpose Weyl argument to `w u X` and
reverses the character. Its exact Haar preservation reduces convergence to the
published positive-level box frame bound. No invertibility condition is
imposed on the Fourier transform of `Φ`.

For the original side, left Weyl translation of `Ψhat`, the identity frame
and the invertible support of `Φ` give the published framed product bound.
Substitution of unipotent inversion preserves its supplied Haar measure
exactly and gives the displayed original kernel. The matrix variable and its
measure remain fixed.

At each fixed unipotent element, bilinear Fourier exchange uses
`B = iota(u) w` and `A = 1`. Both determinants have norm one; the inverse
transpose of `B⁻¹` is precisely `w u⁻¹`. Scalar extraction retains the inverse
standard character on both sides. Product integrability then justifies Fubini.

All results are derived from published actual matrix and Haar constructions,
the full rectangular Fourier theorem and the bilinear Fourier exchange.
No analytic comparison, compact complex measure, model equivalence, or
functional equation is assumed or concluded.
