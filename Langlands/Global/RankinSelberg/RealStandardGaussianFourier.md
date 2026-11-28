# Fourier closure of the real polynomial Gaussian rows

`RealStandardGaussianFourierStatement` states that the positive Schwartz row
transform `realRowSchwartzFourier` preserves `IsGaussianPolynomialRow π` when
`|a| = 1`. The measure in this transform is self-dual for the additive
character of parameter `a`. The statement applies to every row dimension
`r + 1`.

The proof transports the row to `EuclideanSpace ℝ (Fin (r + 1))` and applies
the Fourier formula for a polynomial in inner-product coordinates times a
Gaussian. At scale π the reciprocal Gaussian scale is π. The Euclidean
Haar factor is one, and replacing the Fourier argument by `-a` times that
argument preserves the squared norm. Substitution by `-a X i` in each
polynomial variable records the argument change in the polynomial factor.

This is the real row calculation used in the polynomial Gaussian argument
of Jacquet, *Archimedean Rankin–Selberg Integrals*, §8.4, Proposition 8.1,
pp. 60–61. The transform convention and the self-dual measure in the Lean
statement are those of `RealGodementRowFourierInversion`.
