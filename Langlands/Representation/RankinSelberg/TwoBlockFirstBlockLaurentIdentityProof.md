# Proof of the polynomial-cleared first-block JPSS Laurent identity

Author: Worker 1037. The proof imports published modules authored by Worker 1191:
the scalar FE-coefficient algebra and spectral bridge, and the row-split measure
lemmas. Their interfaces were designed jointly.

This module proves the unchanged published proposition
`Langlands.RankinSelberg.TwoBlockFirstBlockLaurentIdentityStatement.{uF,uV,uW}` as
the theorem `Langlands.RankinSelberg.twoBlockFirstBlockLaurentIdentity`.

## Source

The source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*
(1983), source ID `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`. The relevant
passages are:

- Section 4.6, printed pages 410–412;
- Section 4.7, equation (1), printed page 412;
- Section 4.9, printed pages 416–418.

The implemented route follows the source calculation. All analytic and measure
details are carried out with the actual published integrands and measures.

## Convergence clause

The fixed-slice unfolding `twoBlockFixedSliceUnfolding` supplies the right-invariance
certificate for `μN`, the existence of compatible quotient measures, and a bound `C₁`
depending only on the blocks and their functionals. The lower convergence theorem
`twoBlockLowerFixedSliceConvergence` supplies sigma-finiteness of `νN` and `νMinus`
and a bound `C₂` depending on `π`, `λ`, the blocks and their functionals. The lower
first-block quotient integration theorem supplies the right-invariance of `μNA`,
compatible measures on the small quotient, and sigma-finiteness of `νA`.

The single bound is `max C₁ C₂`. It is chosen after all representations and
functionals and before the twist parameter. For `u` above it and every compatible
pair `νN, νA`, the following hold for every section, coefficient vector and
Schwartz test:

- measurability of the actual radical average `Aup`, by the fixed-slice theorem;
- measurability of the descended lower integrand `Elow`, by the lower convergence
  theorem;
- integrability of both on every determinant slice, by the same two theorems.

The fixed-slice integrability uses a compatible measure on the block quotient, which
exists. These conclusions do not use any epsilon certificate. They hold for zero
functionals.

## Witnesses

For a supplied `UnequalRankEpsilonEquation`, the witnesses `ζ, P, Pdual` are
exactly its own. The minus-one scalar certificate and the entire normalized-generator,
continuation and functional-equation body are returned unchanged. These witnesses
precede all sections, vectors and tests.

## The Laurent identity

Write `a = m 0 + 1` and `b = m 1 + 1`. The finite Laurent action is the published
convolution `(Q • Z)(n) = Σ_i Q_i Z(n - i)`. `D = Pdual(q⁻¹X⁻¹)` is the published
`reflectedPolynomial`.

**Degenerate case.** If `λ = 0` or the first functional vanishes, both integrands
vanish identically, by the Adapters lemmas. Then `Zup = Zlow = 0`, and the identity
is `D • 0 = Q • 0`.

**Nondegenerate inputs.** Otherwise the first block has inverse-character Whittaker
type. This follows from the published twist invariance of Whittaker type and the
standard/inverse equivalence. Both functionals are nonzero, so the published
unequal-rank analytic theorem applies to the original and the transformed small
integrals.

**Measure chain.** In the nondegenerate case fix a slice `k`. Write:

- `f_k` for the actual upper first-block average on the mixed quotient;
- `U_k` for the actual lower radical average of `f_k` for the rectangular measure
  `μR' = rectangularMeasure ν (m 1 + 1) (m 0 + 1)`;
- `L_k` for the actual lower first-block average of `Elow`.

The upper and lower first-block integration theorems use Haar measures `μA0` on
`GL_a^0`. Both satisfy `Subtype.val_* μA0 = μGA|GL_a^0`, so they coincide. One
compatible measure `νM` on the mixed quotient therefore serves both theorems.

The coefficient comparison then reads:

- `Zup(k) = c ∫ Eup = c ∫ f_k = ∫ U_k`. This combines the fixed-slice unfolding, the
  upper equation (6) and the lower equation (2). Here
  `c = rectangularMeasure ν a b (cube)` is the upper cube mass. It equals the lower
  cube mass `rectangularMeasure ν b a (cube)`, by `rectangularMeasure_integer_cube_swap`.
  The upper factor `c` therefore cancels against the lower factor exactly. Equation
  (6) has no density.
- `Zlow(k) = ∫ q^(-k b) L_k`. This is the lower equation (8) with density
  `d = q^(-k b)`; it has no cube factor.

All integrals over the lower mixed quotient are for `νL0`, the restriction of a
compatible measure to the zero slice. All four integrands are integrable by the same
laws.

**Almost-everywhere identity.** The two coefficient families are coefficientwise
integrals over `νL0`. The published `integral_laurent_identity_ae` therefore reduces
the claim to the identity `D • (k ↦ q^(-k b) L_k(z)) = Q • (k ↦ U_k(z))` for almost
every `z`.

For every `k`, the composite lintegral laws of equations (2) and (6) give a.e.
finiteness of the iterated absolute fiber integral of `Eup`
(`ae_lintegral_kernel_comp_lt_top`). At a representative `g` of such a point, the
identity is `pointwise_laurent_identity`. That result combines:

- the row split of the lower rectangle;
- the upper and lower fiber formulas;
- the reflection of the small quotient;
- the per-row published `smallFE_coefficient_identity`, for the translates
  `R(0; x) g` of the test vector and the first-block coefficient function of `f(g)`.

**Coefficient functions.** For a row `x` and the representative `g`, let `F_g` be
the first-block coefficient function of `f(g)`. Then:

- `a_x(k)` is the actual slice coefficient `∫_{AQ_k} ∫_y` of the original small
  integrand at `s = 0` for the pair `(W(· R(0; x) g), F_g)`, with the supplied
  rectangular product measure.
- `a'_x(k)` is the same slice coefficient for the transformed pair: the translate by
  `blockWeylAt` of the first dual function, and the second dual function. These are
  taken for the inverse character and the zero-row rectangle.
- `reflectSeries q a'(n) = q^n a'(-n)`.

The upper coefficient is `∫_x Φ((x, η) g) a_x(k)`. The lower coefficient is
`∫_x Φ((x, η) g) reflectSeries q a'_x(k)`.

The original block `j = m 1`, `k = 0` is used, including when either block has size
one. No polynomial factor is cancelled on the bilateral series module. The supplied
self-dual measure is used throughout without renormalization.

## Helper modules

The proof uses the helper modules `TwoBlockFirstBlockLaurentSlices`, `Sections`,
`Matrices`, `Involution`, `Fourier`, `Integrands`, `Convergence`, `Coefficients`,
`Pointwise` and `Adapters` of this candidate. Each has its own Markdown file. It also imports the published modules
`TwoBlockFirstBlockLaurentAlgebra`, `Reflection`, `TwoBlockSmallFunctionalEquationLaurentBridge`
and `TwoBlockFirstBlockLaurentRowSplit`.

The proof does not use unrestricted multiplicativity, finite-block parents, the
Section 7 assembly, Section 9.3, the Section 4.8 companion comparison, the strictly
dominant Section 4.10 argument, deformation specialization or dominant-rank
gamma/L conclusions.
