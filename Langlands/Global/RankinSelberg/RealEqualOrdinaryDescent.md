# Descent from real equal-rank ordinary integrals

`RealEqualOrdinaryDescentStatement` takes continuous real Whittaker functions
`W` and `V` on `GL_(n+2)` with opposite left characters and simple-root gauge
bounds. For compatible unipotent quotient measures in the two ranks, assume
that the ordinary equal-rank integral of `W`, `V` and each Schwartz row test
vanishes on a right half-plane that may depend on the test. Then the ordinary
`GL_(n+2) × GL_(n+1)` integral of `W` and `V` restricted to the standard
leading block vanishes on a right half-plane.

The proof fixes a compactly supported smooth row test equal to one at the
standard last row. Multiplication by any Fourier character preserves its
absolute value and gives another Schwartz test. Convergence for the fixed
test supplies the absolute bounds that make all its modulated integrals
holomorphic on a common right half-plane. The identity theorem transfers the
assumed vanishing to that half-plane.

`RealOrdinaryRowLocalization.realOrdinaryRowLocalization` now forces the
leading-block fibre at the standard last row to vanish. For a row `(x,u)`,
the chart writes the integrand at `diag(g,1) L(x,u)` with
`L(x,u) = [[1,0],[x,u]]`. The determinant density `|det g|⁻¹` lowers the
leading-block determinant exponent by one. With the adjacent-rank
Rankin–Selberg convention, the fibre is the integral of the translated
functions at `s - 1/2` times the row test and `|u|^s`. The translated
adjacent-rank integral is continuous at `L = 1` by uniform gauge estimates
on a compact neighborhood and dominated convergence. At the standard row
both scalar factors are one and `L = 1`, yielding the asserted vanishing.

Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §14.2, proof of
Lemma 14.1, author-posted pp. 105–107, uses the same last-row measure and
`|det g|^(s-1)` in the passage from equal rank to the leading block. The
Lean argument derives vanishing descent using Fourier localization, with
fixed coefficients and varying Schwartz row tests.
