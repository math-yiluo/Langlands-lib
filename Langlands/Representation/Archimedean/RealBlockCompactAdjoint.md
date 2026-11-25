# Adjoint block Fourier multipliers in the compact principal-series model

This internal derived module uses the existing normalized Haar inner product on
`PrincipalSeriesAnnihilator.KFin n χ`. It introduces no literature premise.

`RealBlockCompactAdjointStatement` quantifies arbitrary rank `n`, position `p` with
`p + 1 < n`, character family `χ`, compact-finite principal-series vectors
`x, x', y, y'`, and sequence `μ : ℤ → ℂ`. If the block Fourier coefficients
of `x'` are `μ(j)` times those of `x`, and those of `y'` are `conj(μ(j))`
times those of `y`, on the compact group, then
`⟪x', y⟫ = ⟪x, y'⟫`. The inner product is conjugate linear in its first input.
`realBlockCompactAdjoint` proves this proposition.

The namespace `RealBlockCompactAdjoint` also supplies these helpers:

- `conjugate` is pointwise complex conjugation as a semilinear map.
  `conjugate_mem_kFiniteVectors` proves that it preserves right `O(n)` finiteness.
- `inner_eq_of_multiplier` is the quantified adjoint identity above.
- `inner_eq_of_real_multiplier` specializes it to self-adjoint endomorphisms with
  real multiplier values.
- `eq_of_fourier` identifies two compact-finite vectors in the same principal series
  from equality of their block Fourier coefficients on `O(n)`.

For conjugate finiteness, conjugation maps the span of the original right compact
orbit to the span of its conjugate orbit. A semilinear map preserves finite
generation, hence finite dimension over `ℂ`. The adjoint proof applies the
published bilinear transposition formula
`RealBlockTransposition.integral_mul_eq_of_multiplier` to `conj(x)`, `conj(x')`,
`y`, and `y'`, with multiplier `j ↦ conj(μ(-j))`. The published conjugation formula
`RealSwapFLanding.blockFourierCoefficient_conj` reverses each Fourier index and
conjugates the coefficient, giving exactly the two required multiplier identities.
The compact inner product is its defining Haar integral. Fourier uniqueness uses
finite Fourier inversion on the compact group and principal-series uniqueness
from restriction to that group.

This module supplies compact harmonic analysis for the filtration of the `GL_4(ℝ)`
standard module of two induction blocks. It does not identify
an intertwiner's range or prove the two-induction-block filtration.
