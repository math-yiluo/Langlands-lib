# Plancherel in real coordinates

`coordinateFourierIntegral` uses the phase `exp(i ∑ zⱼ yⱼ)` and Lebesgue
measure on `Fin m → ℝ`. `CoordinatePlancherelStatement` gives square
integrability of both transforms and identifies their pairing with
`(2π)^m` times the original pairing. Both inputs are complex-valued
functions in `L¹ ∩ L²`, and the pairing conjugates the second factor.

`ae_fourier_toLp_eq` compares the Fourier integral to Mathlib's `L²`
Fourier transform on a finite-dimensional real inner product space.
Both representatives are locally integrable. The proof embeds each
smooth compactly supported real test function into the complex Schwartz
space, uses the Fourier identity for tempered distributions, and moves
the Fourier integral across the bilinear test pairing by Fubini.
Equality against all such tests gives almost-everywhere equality.

`coordinatePlancherel` uses `Lp.inner_fourier_eq` with the two inputs
in the order required by Mathlib's inner product. The canonical
volume-preserving map from the coordinate space to Euclidean space
expresses the positive-phase integral as the ordinary Fourier transform
at `−y/(2π)`. The Haar measure scaling for this dilation preserves
square integrability and contributes `(2π)^m` to the pairing.

The coordinate identity isolates the scalar Plancherel step for the
Fourier transform on the split centre in E. Lapid, *On Arthur's
asymptotic inner product formula of truncated Eisenstein series*
(2011), §8, printed p.328 (volume PDF p.337). The coordinates here use
unscaled Lebesgue measure. The spectral measure factors enter when
applying this identity to the wave packet integrals.
