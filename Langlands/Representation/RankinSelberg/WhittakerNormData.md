# Pointwise norm data on the left-unipotent quotient

Author: Worker 594.

This is a derived construction from the published definitions in
`Langlands.Representation.RankinSelberg.QuotientIntegrals`, the unitary
characters in `Langlands.Representation.Whittaker.GeneralLinear`, and the
actual left-coset descent in `Langlands.Analysis.Local.QuotientMeasure`.
Those published Lean/Markdown pairs are imported unchanged. No additional
representation, quotient, or additive-character interface is introduced.

For any field `F : Type uF`, with independent universe `uF`, the existing
`LeftUnipotentQuotient n F` is the left coset space
`N_(n+1) \ GL_(n+1)`. The two constructions needing no topology are:

- `quotientDeterminantAbs abv n`, a real-valued function whose value at `[g]`
  is `abv (Matrix.det g.val)`, for a supplied `AbsoluteValue F ℝ`;
- `quotientLastRow n`, with values in `Fin (n + 1) → F`, whose value at `[g]`
  is the existing `lastRow g`.

Given a topology on `F` and the existing unitary additive character `ψ`, the
remaining three real-valued functions are:

- `whittakerNorm ψ W`, with value `‖W.val g‖`, for
  `W : WhittakerFunctions ψ n`;
- `inverseWhittakerNorm ψ W'`, with value `‖W'.val g‖`, for
  `W' : InverseWhittakerFunctions ψ n`;
- `restrictedWhittakerNorm ψ k W`, with value
  `‖W.val (appendIdentity n (0 + k + 1) g)‖`, for
  `W : WhittakerFunctions ψ (n + (0 + k + 1))`.

The last rank expression is preserved literally to match the zero-row
`unequalRankModelIntegral` convention. The smaller matrix has rank `n + 1`,
the larger has rank `n + (0 + k + 1) + 1`, and the appended identity block
has size `0 + k + 1`. In source notation these are `t`, `r`, and `r - t`.
There are no nonzero-function assumptions or positive lower bounds on `n`
or `k`. Thus `n = 0` includes smaller rank one and `k = 0` includes the
corank-one restriction. All three Whittaker norm functions have proved
`_zero` identities.

The construction proves representative independence before applying
`QuotientIntegration.descend`. `determinantAbs_unipotent_mul` uses the
published theorem that an upper-unipotent matrix has determinant one and
multiplicativity of the determinant. `quotientLastRow` uses the published
`lastRow_unipotent_mul`. `whittakerNorm_invariant` uses Whittaker covariance,
multiplicativity of the complex norm and `norm_standardCharacter`.
`inverseWhittakerNorm_invariant` uses the inverse-character formula and the
norm of an inverse. `restrictedWhittakerNorm_invariant` applies standard
norm invariance to `appendUnipotent` and uses `appendUnipotent_val` and the
homomorphism law of `appendIdentity`. Unitarity alone is enough here; no
estimate is needed.

Each construction has a proved `_mk` evaluation theorem on quotient classes.
All four real-valued functions have pointwise `_nonneg` theorems.
`quotientDeterminantAbs_pos` is strictly positive on every class because
an invertible matrix has nonzero determinant and an absolute value is
positive away from zero. These properties are proved by quotient induction.

The original notation motivating this API is in H. Jacquet,
I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin–Selberg Convolutions*,
American Journal of Mathematics 105 (1983), 367–464, §8.3, printed
pp.448–451 (retained PDF pages83–86, one-based). Registered source:
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
All four pages were read directly from the scan. In particular, p.449 uses
`|W(diag(g,1))|²` and `|det g|⁻¹`; p.450, equation (7) and the following
zero-row integral, uses the restricted Whittaker function, determinant
powers and the last row `η_t g`; and p.451 uses products of the two
Whittaker norms with a test function of the last row.

The source places these expressions in analytic arguments about
square-integrable representations over non-archimedean local fields. This
module only constructs their pointwise quotient data, derived from the
published algebraic definitions, over arbitrary fields with the topology
needed to supply `ψ`. It proves no norm integrability, square-integrability
comparison, compact-support estimate, convergence, or holomorphy assertion.
