# Linearity and covariance laws of the actual unequal-rank integrals

Authors: Worker 822 (Lean) and Worker 233 (Markdown). Part of the proof task
`4564f536-d9dc-4d9a-aeb5-4ee980417bd3` for the published statement
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`; its
consumers are `UnequalRankBlockZeroContinuationFamily`,
`UnequalRankBlockZeroCovariance` and `UnequalRankBlockZeroContinuedFormsProof`.

This module proves, for an arbitrary block `(j, k)`, the linearity laws and
two transformation laws of the Library's actual iterated JPSS integral
`unequalRankIntegral ψ abv j k μ ρ W W' s`. The setting is general: a field `F`
with a topology, an absolute value `abv`, any measurable structures and
measures `μ` on the quotient `LeftUnipotentQuotient n F = N \ GL_(n+1)(F)` and
`ρ` on the rectangular variables `Matrix (Fin j) (Fin (n + 1)) F`. Nothing
published is redefined. The module uses `unequalRankIntegrand`,
`unequalRankIntegral`, `UnequalRankConverges`, `unequalRankMatrix`,
`appendIdentity`, `determinantWeight` and `rightTranslate` as published.

Throughout, `W, W₁, W₂` are Whittaker functions on `GL_(n+j+k+2)`, `W', W'₁,
W'₂` inverse Whittaker functions on `GL_(n+1)`, and `c, s` complex numbers.
Write `M(g, x) = unequalRankMatrix j k g x` and `|det g|^t` for
`determinantWeight abv g t`. By the published `unequalRankIntegrand_mk`, the
integrand at the rectangular variable `x` and the class of `h` is
`W(M(h, x)) W'(h) |det h|^(s - (j+k+1)/2)`, and the integral is
`∫ q, ∫ x, integrand x q ∂ρ ∂μ` (Bochner integrals, rectangular variable
inside).

## Linearity

- `unequalRankIntegrand_add_left`, `unequalRankIntegrand_add_right`,
  `unequalRankIntegrand_smul_left`, `unequalRankIntegrand_smul_right`: at
  every point `(x, q)` the integrand is additive and homogeneous in each
  function. Proof: induction on the quotient class, `unequalRankIntegrand_mk`,
  `ring`.
- `unequalRankIntegral_add_left`, `unequalRankIntegral_add_right`: if
  `μ` and `ρ` are s-finite and both summands converge absolutely at `s`
  (`UnequalRankConverges`, integrability of the integrand on `μ.prod ρ`), the
  integral of the sum is the sum of the integrals. Proof: pointwise
  additivity, then Mathlib's `integral_integral_add`. No other hypothesis on
  the measures is used.
- `unequalRankIntegral_smul_left`, `unequalRankIntegral_smul_right`: the
  integral of `c • W` (resp. `c • W'`) is `c` times the integral, at every
  `s`, with no convergence or finiteness hypothesis (`integral_const_mul`).

## Inner change of variables

`unequalRankIntegral_of_inner_change`: let
`φ : Matrix (Fin j) (Fin (n + 1)) F → Matrix (Fin j) (Fin (n + 1)) F` and
`c : ℂ`. Assume

- `W₂(M(g, x)) = c · W₁(M(g, φ x))` for all `g` and `x`, and
- `∫ G (φ x) ∂ρ = ∫ G x ∂ρ` for every function `G` (`φ` preserves Bochner
  integrals against `ρ`).

Then `unequalRankIntegral … W₂ W' s = c · unequalRankIntegral … W₁ W' s` for
every complex `s`. Proof: the first hypothesis makes the integrand of `W₂` at
`(x, q)` equal to `c` times the integrand of `W₁` at `(φ x, q)`, and the
second hypothesis removes `φ` from the inner integral. The Covariance module
proves both unipotent laws (JPSS (2.11.4)) with this lemma. For the original
integral `φ` is the identity. For the complementary integral `φ x = A x + c`
with `det A = 1`, from `dualUnipotent_identity`.

## Right translation

This section assumes `[IsTopologicalRing F]` (for `rightTranslate`) and a
Borel measurable structure on the quotient.

- `determinantWeight_exponent_add`: `|det g|^(s + t) = |det g|^s |det g|^t`
  (`Complex.cpow_add`; the base `abv (det g)` is nonzero).
- `unequalRankIntegrand_translate`: assume `W₂(h) = W₁(h · diag(g, I))` and
  `W'₂(h) = W'₁(h g)` for all `h`, where `diag(g, I) = appendIdentity n
  (j+k+1) g`. Then at every `(x, q)` the integrand of `(W₂, W'₂)` equals
  `|det g|^((j+k+1)/2 - s)` times the integrand of `(W₁, W'₁)` at
  `(x g, q g)`. Proof: `M(h, x) · diag(g, I) = M(h g, x g)`
  (`unequalRankMatrix_mul_appendIdentity`), then the published
  `determinantWeight_mul` and `determinantWeight_neg_mul_self`.
- `unequalRankIntegral_translate`: assume moreover that right translation by
  every `g` preserves `μ` and that the rectangular measure scales by
  `|det g|^(-j)`:

  `∫ G (x g) ∂ρ = |det g|^(-j) · ∫ G x ∂ρ` for every function `G`.

  Then for every complex `s`,

  `unequalRankIntegral … W₂ W'₂ s = |det g|^((j+k+1)/2 - s - j) ·
  unequalRankIntegral … W₁ W'₁ s`.

  Proof: the pointwise law, the scaling hypothesis on each inner integral,
  and `MeasurePreserving.integral_comp` for the measurable embedding
  `rightTranslate g` on the outer integral. No convergence is needed, because
  all three steps are identities of Bochner integrals of arbitrary functions.
  The Proof module supplies the scaling hypothesis in the two cases used. For
  `j = 0` the rectangular measure on the empty matrices is the unit point
  mass, so it holds trivially (`rectangularMeasure_zero_rows_translate`). For
  the complementary integral, `j = k`, it holds by the published p-adic
  rectangular Haar scaling `padicRectangularHaarScaling`.

## Provenance

JPSS = H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), §2.11, printed pp.398–399
(one-based PDF pages 33–34 of the registered scan `jpss-1983-rankin-selberg`).
The two transformation laws here are general-`(j, k)` versions of the
computations behind JPSS (2.11.2) and (2.11.4), which JPSS states for `j = 0`
and the complementary integral "as before", without proof (compare the
analogous change-of-variables computations in §2.10, pp.395–397). With printed
ranks `r, t` equal to Lean `r + 1, n + 1` and `j = 0`, the exponent
`(j+k+1)/2 - s - j` is `(r-n)/2 - s`, the exponent `(r-t)/2 - s` of (2.11.2).
The formulation with explicit hypotheses on `μ` and `ρ`, valid at every
complex `s` as identities of Bochner integrals, and the inner-change lemma
are internal to this proof. The linearity laws are elementary and not stated
in JPSS. The current registration, the central library, and the project and
Library note locations were checked for errata. No registered erratum to JPSS
1983 was found. The registered Jacquet 2012 correction concerns the 1981
conductor paper only.
