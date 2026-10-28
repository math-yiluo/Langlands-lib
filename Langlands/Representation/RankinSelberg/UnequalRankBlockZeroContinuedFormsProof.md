# Continued unequal-rank bilinear forms at block zero

Authors: Worker 822 (Lean proof and this explanation) and Worker 233 (reading
of JPSS §2.11 and the errata check in the provenance section).

The paired Lean file proves

```text
theorem Langlands.RankinSelberg.unequalRankBlockZeroContinuedForms {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankBlockZeroContinuedFormsStatement.{uF, uV, uW} F T n r
```

with independent universes `uF`, `uV`, `uW`. The statement is the published
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`; its
Lean/Markdown pair is unchanged.

## Hypotheses used

After the statement's instances are installed, the proof uses only:

- the two analytic premises, the original `UnequalRankAnalyticAt 0 k` (`hA`)
  and the inverse-transpose `UnequalRankAnalyticAt k 0` (`hAd`), with
  `k = r-n-1`;
- two fields of `IsCompatible` for the supplied quotient measure `μ`:
  `right_invariant` (right translation by every `g ∈ GL_(n+1)` preserves `μ`)
  and `regular`;
- the supplied scalar Haar measure `ν`, through the rectangular product
  measures `rectangularMeasure ν 0 (n+1)` and `rectangularMeasure ν k (n+1)`;
- facts about the p-adic field itself: `1 < q` for
  `q = T.residueCardinality`, `|det g| = q^m` with `m ∈ ℤ` for the normalized
  absolute value, second countability and sigma-compactness, and the published
  rectangular Haar scaling theorem `padicRectangularHaarScaling`.

The Whittaker-type hypotheses on `π` and `σ`, the nonvanishing of `ℓ` and
`ℓ'`, the right-invariance instance for `unipotentHaar`, and the
nonarchimedean instance are not needed, so they are left unused. The proof
therefore covers the full stated scope: reducible representations, every
compatible quotient measure and every scalar additive Haar measure. It uses no
irreducibility, central character, uniqueness, functional equation, gamma or
epsilon factor, comparison scalar, or generator shared between blocks.

## Modules

The entry module imports the target statement, `PadicRectangularHaarScalingProof`
(rectangular Haar scaling), `Group.GL.CountabilityProof` (sigma-compactness of
`GL_(n+1)`), and the following four helper modules. The helpers are new, ship
in the same submission, and each has its own Markdown:

- `UnequalRankBlockCoordinates`: block coordinates `Fin (n+1) ⊕ Fin m` and the
  matrix identities behind (2.11.2) and (2.11.4).
- `UnequalRankBlockZeroIntegralLaws`: linearity of the actual integrals, the
  general right-translation law, and an inner change-of-variables law.
- `UnequalRankBlockZeroContinuationFamily`: the bilinear family of rational
  continuations and its pointwise evaluation.
- `UnequalRankBlockZeroCovariance`: the covariance laws of the original and
  dual integrals, and of their continuation families.

Through the helper modules, the published `EqualRankContinuedFormsProof`,
`EqualRankContinuationFamily`, `LaurentEvaluation` and `RationalEvaluation`
are imported. From them the proof reuses
`normalizedAbsoluteValue_det_eq_zpow`, `padic_row_instances` (sigma-finiteness
of `ν`), `determinantWeight_neg_eq_spectralPoint_zpow`,
`spectralPoint_sub_one_sub`, and the `RegularAt`/`eval_*` lemmas for rational
evaluation.

## The two actual integral families

Write `M = (coefficientModel π ℓ).toSubmodule` and
`M' = (coefficientModel σ ℓ').toSubmodule`. The original family is

```text
I(f,f')(t) = unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (n+1))
               f.val f'.val t.
```

The dual family is the statement's `dualUnequalRankModelIntegralAt hnr 0 k hr
… f f'`. By definition it is the block `(k,0)` integral, for the character
`ψ.scale (-1)`, of the two dual vectors

```text
dualFirstModelMap ψ π ℓ hnr f = translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f
secondDualModelMap ψ σ ℓ' f'.
```

The first is `h ↦ f(w_(r+1) (h·w_(r,t))⁻ᵗ)` with `w_(r,t) = blockWeylAt n r hnr`.
The second is `h ↦ f'(w_(n+1) h⁻ᵗ)`. Both maps are the published complex-linear
maps of `DualModels` into the actual inverse-transpose coefficient models, so
the dual analytic premise `hAd` applies to these vectors. No surrogate family
is introduced.

## Step 1: bilinear families of rational continuations

`blockContinuationFamily hq hA : M →ₗ[ℂ] M' →ₗ[ℂ] RationalFunctions` (in
`UnequalRankBlockZeroContinuationFamily`) sends `(f,f')` to a rational
continuation of `I(f,f')`. The continuation is chosen from `hA`, and by
`HasRationalContinuation.unique` (which needs `1 < q`) it is the only one.

Bilinearity is an identity of rational functions; no rational function is
evaluated anywhere in this step. For additivity in `f`, the premise gives a
right half-plane of absolute convergence for each of `(f₁,f')` and
`(f₂,f')`. On the intersection of the two half-planes,
`unequalRankIntegral_add_left` gives
`I(f₁+f₂,f') = I(f₁,f') + I(f₂,f')`. This is Fubini additivity of the iterated
integral, which needs `SFinite μ` and `SFinite` of the rectangular measure. So
the sum of the two continuations continues `I(f₁+f₂,f')` (`continuation_add`,
`continuation_of_eq_on_right`), and uniqueness identifies it with the chosen
continuation. Homogeneity holds for every `t`, because the integral is
homogeneous. The second variable is handled the same way.

The dual family `dualBlockContinuationFamily hnr hq hAd` is
`blockContinuationFamily hq hAd` precomposed in each variable with
`dualFirstModelMap` and `secondDualModelMap` (`LinearMap.compl₁₂`). It is
therefore bilinear on the original models `M × M'`.

## Step 2: the uniform finite exceptional set

Each premise supplies a normalized generator: `P` for the original values and
`Pd` for the dual values (`UnequalRankAnalyticAt.exists_normalizedGenerator`).
`IsNormalizedGenerator values P` says that `P(0) = 1` and that the zeta span of
`values` over the Laurent polynomials is generated by `1/P`. Every value of a
family lies in the actual value set, by `unequalRankValuesAt_eq_set`. Hence
`IsNormalizedGenerator.clearsDenominators` shows that `P · R` is a Laurent
polynomial for every family value `R` (`blockContinuationFamily_clears`,
`dualBlockContinuationFamily_clears`).

A Laurent polynomial is regular at every nonzero point. So
`regularAt_of_clears` gives: if `z ≠ 0` and `P(z) ≠ 0`, then every family value
`R` satisfies `RegularAt R z`, which means that its reduced denominator does not
vanish at `z`.

The proof takes

```text
E = P.roots.toFinset ∪ Pd.roots.toFinset.image (fun w => ((q : ℂ) * w)⁻¹).
```

`E` is a finite set of complex numbers built only from `P`, `Pd` and `q`. It
is chosen before `s`, the model vectors, the continuations and the covariance
translations. Suppose `spectralPoint q s = q^(-s)` is not in `E`. Then
`P(q^(-s)) ≠ 0`. Also `Pd(q^(-(1-s))) ≠ 0`, because
`spectralPoint_reflect` gives `(q · q^(-(1-s)))⁻¹ = q^(-s)`: the map
`w ↦ (q w)⁻¹` sends the dual spectral point to the original one. This uses
`spectralPoint_sub_one_sub`, `q^(-(1-s)) = q⁻¹ (q^(-s))⁻¹`. Both spectral points are
nonzero because `q > 0` (`spectralPoint_ne_zero_of_pos`). So every value of the
original family is regular at `q^(-s)`, and every value of the dual family is
regular at `q^(-(1-s))`.

## Step 3: the forms and the evaluation clauses

For `spectralPoint q s ∉ E` the forms are

```text
B     = evalForm (blockContinuationFamily hq hA)               (q^(-s))      _
Bdual = evalForm (dualBlockContinuationFamily hnr hq hAd)      (q^(-(1-s)))  _
```

`evalForm C z hreg` is `(f,f') ↦ RatFunc.eval z (C f f')`, built with
`LinearMap.mk₂`. It is complex bilinear because evaluation is additive and
multiplicative at points where all the rational functions involved are regular
(`eval_add`, `eval_mul`, `eval_smul_of_regularAt`). The regularity hypothesis
`hreg` is exactly Step 2. Bilinearity of the families comes from Step 1, so it
is never derived by evaluating at a pole.

Evaluation clauses. Let `R` be any rational continuation of `I(f,f')`. By
uniqueness, `blockContinuationFamily_eq` gives `blockContinuationFamily hq hA f
f' = R`. So `R.denom.eval (q^(-s)) ≠ 0` by Step 2, and `B f f'` is by
definition `RatFunc.eval (q^(-s)) R`. In the same way, let `Rd` be any
continuation of `dualUnequalRankModelIntegralAt hnr 0 k hr … f f'`, taken at
its unreflected parameter. Then `dualBlockContinuationFamily_eq` gives family
value `Rd`, so `Rd.denom.eval (q^(-(1-s))) ≠ 0` and
`Bdual f f' = RatFunc.eval (q^(-(1-s))) Rd`. Neither clause uses a continuation
of the other integral, and neither evaluation is normalized.

## Step 4: covariance by changes of variables

All integral identities below hold for every complex `t`, as identities of the
actual iterated integrals against `μ` and the rectangular measures. They do
not require convergence. A law `I₂(t) = c · (q^(-t))^m · I₁(t)` for all `t`
transfers to the continuations as `R₂ = C c · X^m · R₁`
(`blockContinuationFamily_of_integral`, by `HasRationalContinuation.monomial_mul`
and uniqueness). At a nonzero regular point `z`, evaluation gives
`eval z (C c · X^m · R₁) = c · z^m · eval z R₁` (`eval_C_mul_X_zpow_mul`).
`habv` writes `|det g| = q^m` with `m = -ord(det g)`, and then
`determinantWeight_neg_eq_spectralPoint_zpow` gives `|det g|^(-t) = (q^(-t))^m`.

### General-linear law (2.11.2)

`unequalRankIntegral_translate` (in `UnequalRankBlockZeroIntegralLaws`) treats
block `(j,k)`. Replace `W` by its right translate by `diag(g, I)` and `W'` by
its right translate by `g`. The block matrix satisfies
`[h,0;x,1] · diag(g,I) = [hg,0;xg,1]` (`unequalRankMatrix_mul_appendIdentity`).
Splitting the determinant weight gives the pointwise factor
`|det g|^((j+k+1)/2 - t)`. The integrand is then evaluated at `xg` and at the
right translate of the quotient point. The change of variables `x ↦ xg` in
the rectangular integral contributes `|det g|^(-j)`; this law is a hypothesis
of the lemma. The quotient change of variables is exact by
`IsCompatible.right_invariant`. So the integral is multiplied by
`|det g|^((j+k+1)/2 - t - j)`.

- Original block `(0,k)`: the zero-row space has the single point `x = 0`,
  so `x g = x` and `|det g|^0 = 1` (`rectangularMeasure_zero_rows_translate`).
  The factor is `|det g|^((r-n)/2 - t)`. Evaluating the continuation family at
  `t = s` gives exactly `determinantWeight abv g (((r-n : ℕ) : ℂ)/2 - s)`.
- Dual block `(k,0)`: translating `f` by `diag(g,I)` and `f'` by `g` translates
  the two dual functions by `diag(g⁻ᵗ, I)` and `g⁻ᵗ`. For the first dual function
  this takes three identities. `blockWeylAt_mul_embedding` commutes `diag(g,I)`
  past `w_(r,t)`. `inverseTranspose_embedding` identifies the inverse transpose
  of `diag(g,I)` as `diag(g⁻ᵗ,I)`. These two combine in
  `inverseTranspose_mul_embedding`. Applying the general law with `g⁻ᵗ` needs
  `∫ G(x g⁻ᵗ) dρ = |det g⁻ᵗ|^(-k) ∫ G dρ` for `ρ = rectangularMeasure ν k (n+1)`.
  The factor is `|det g⁻ᵗ|^((k+1)/2 - t - k) = |det g|^(t + (k-1)/2)`
  (`determinantWeight_inverseTranspose`). At `t = 1-s` this is
  `|det g|^((k+1)/2 - s) = |det g|^((r-n)/2 - s)`, since `k+1 = r-n`.
  This is the same weight as for `B`, at the same `s`.

### Unipotent law (2.11.4)

Let `u ∈ upperUnipotent (r+1)` satisfy `IsUnequalRankCovarianceUnipotent n u`:
the leading `(n+2)`-square block of `u` is the identity. In block coordinates
`(n+1) + (r-n)`, `u = [1, Q; 0, D]`, where `D` is upper unitriangular
(`covarianceUnipotent_blocks`) and the first column of `Q` vanishes
(`toBlocks₁₂_covarianceUnipotent_zero`). Both laws come from
`unequalRankIntegral_of_inner_change`. Suppose `W₂(m(g,x)) = c · W₁(m(g,φ x))`
for all `g, x`, and `φ` preserves integrals against the rectangular measure.
Then the integrals differ by the factor `c` for every `t`.

- Original block `(0,k)`: here `m(g,0) = diag(g,I)`, and
  `originalUnipotent_identity` gives `diag(g,I) u = u' diag(g,I)` with
  `u' = [1, gQ; 0, D] ∈ U_(r+1)`. The first-superdiagonal sums of `u'` and `u`
  agree, because the junction entry `(gQ)_(n,0)` is zero. The Whittaker
  property of `f` gives the factor `ψ_r(u') = ψ_r(u)`, with `φ = id`.
- Dual block `(k,0)`: right translation of `f` by `u` right translates the
  first dual function by `u⁻ᵗ`. `dualUnipotent_identity` gives
  `m(g,x) · w_(r,t) · u⁻ᵗ = n₀ · m(g, A x + c) · w_(r,t)`. Here `n₀ ∈ U_(r+1)`,
  the matrices `A` and `c` do not depend on `g` or `x`, `A` is upper
  unitriangular (so `det A = 1`), and the first-superdiagonal sum of `n₀` is
  minus that of `u`. The dual function is a Whittaker function for the inverse
  character `ψ.scale (-1)`, so `n₀` contributes `ψ(-(-Σ u_(i,i+1))) = ψ_r(u)`.
  The inner change is `φ x = A x + c`. It preserves the rectangular integral by
  the affine law below.

For both forms the continuation is multiplied by `C(ψ_r(u)) · X^0`, so
evaluation at the regular point gives the factor `standardCharacter ψ r u`.

### The two rectangular measure laws

`padic_rectangular_laws` proves both laws for `rectangularMeasure ν k (n+1)`
and every additive Haar measure `ν`. Both come from
`padicRectangularHaarScaling`, which says that `X ↦ A X B⁻¹` scales a
rectangular additive Haar measure by
`(‖det A‖^(n+1) / ‖det B‖^k)⁻¹`. Here `‖·‖` is the residue-normalized
determinant norm, which equals the normalized absolute value of the
determinant.

- Right scaling: with `A = 1` and `B = g⁻¹` the measure maps to
  `|det g|^(-k) · ρ`. `integral_comp_of_map_eq_smul` turns this into
  `∫ G(x g) dρ = |det g|^(-k) ∫ G dρ`, which is written as
  `determinantWeight abv g (-k)`.
- Affine invariance: if `det A = 1`, then with `B = 1` the scaling factor is
  `1`, so left multiplication by `A` preserves `ρ`. Translation `x ↦ x + c`
  preserves any additive Haar measure (`map_add_right_eq_self`), and
  `integral_affine_eq_self` combines the two.

### Sigma-finiteness of the measures

`padic_quotient_sigmaFinite` shows that every regular measure on
`LeftUnipotentQuotient n F` is sigma-finite. The quotient is the image of the
sigma-compact group `GL_(n+1)` under the continuous quotient map, so it is
sigma-compact. A regular measure is finite on compact sets, and so it is
sigma-finite on a sigma-compact space. This applies to `μ` by
`IsCompatible.regular`. The rectangular measures are sigma-finite because `ν`
is (`padic_row_instances`, `rectangularMeasure_sigmaFinite`).

## Assembly

`blockZeroContinuedForms_of_laws` carries out Steps 1–4 over a general
topological field. It takes as explicit hypotheses the right invariance of
`μ`, integrality of `log_q |det g|`, and the two rectangular measure laws of
block `k`. It proves `UnequalRankBlockZeroContinuedFormsConclusion`. The final
theorem `unequalRankBlockZeroContinuedForms` installs the statement's
instances and discharges these hypotheses for the p-adic field:

- `T.residueCardinality_gt_one` gives `1 < q`.
- `normalizedAbsoluteValue_det_eq_zpow` gives `|det g| = q^m`.
- `padic_rectangular_laws` gives the two rectangular measure laws.
- `padic_quotient_sigmaFinite` and `padic_row_instances` give
  sigma-finiteness.

## Provenance: JPSS section 2.11

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), 367–464, §2.11, printed
pp.398–399. These are one-based PDF pages 33–34 of the registered scan
`jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The scan has no text layer, so the pages were read visually, independently by
both authors. The printed ranks `r, t` are Lean `r+1, n+1`. So printed `r-t`
is Lean `r-n`, and printed `r-t-1` is Lean `k = r-n-1`.

- §2.11 assumes `t ≤ r-1` and, by the remark in (2.8), `j = 0`. Formula
  (2.11.1) is the block-zero integral
  `Ψ(s, W, W'; 0) = ∫_{N_t\G_t} W[diag(g, 1_{r-t})] W'(g) |det g|^{s-(r-t)/2} dg`.
  In Lean it is `unequalRankIntegralAt 0 k hr ψ abv μ (rectangularMeasure ν 0 (n+1)) f f'`.
  With zero rows the rectangular measure is the unit point mass. So this is
  the integral, against the supplied compatible quotient measure `μ`, of
  `f(diag(g, I_(r-n))) f'(g) |det g|^(z-(r-n)/2)`.
- Formula (2.11.2) says that, "except for finitely many `q^{-s}`",
  `Ψ(s, π(g)W, π'(g)W'; 0) = |det g|^{(r-t)/2-s} Ψ(s, W, W'; 0)`, "and
  similarly for `Ψ(1-s, ρ(w_{r,t}) W̃, W̃'; r-t-1)`". This is the
  general-linear clause of `IsUnequalRankBilinearCovariant`, with exponent
  `((r-n : ℕ) : ℂ)/2 - s`, for both `B` and `Bdual` at the same `s`.
  Substituting `g ↦ gh` in (2.11.1) produces the factor `|det h|^{(r-t)/2-s}`,
  so the sign is right. In Lean the complementary integral is
  `dualUnequalRankModelIntegralAt`, evaluated at `1-s`. It has block `(k,0)`
  with `k = r-n-1` rectangular rows and the inverse character `ψ.scale (-1)`.
  It uses the inverse-transpose functions `firstDualFunction` and
  `secondDualFunction`, and the first is right translated by
  `w_{r,t} = blockWeylAt n r hnr`. Both rectangular measures come from the
  same supplied scalar Haar measure `ν`.
- Formula (2.11.3) defines `U_{t,r}` as the matrices `(1_t u₂; 0 u₁)` with
  `u₂ ∈ M(t × (r-t))` and `u₁ ∈ N_{r-t}`. Formula (2.11.4) says
  `Ψ(s, π(u)W, W'; 0) = θ_r(u) Ψ(s, W, W'; 0)` for `u ∈ U_{t+1,r}`, and
  "similarly" for the complementary integral. In Lean, `U_{t+1,r}` is
  `IsUnequalRankCovarianceUnipotent n u`: the leading `(n+2)`-square block of
  `u : upperUnipotent (r+1)` is the identity. `θ_r` is `standardCharacter ψ r`.
  Both forms get the same character.
- JPSS states (2.11.2) and (2.11.4) without separate proof. It then derives
  the functional equation (2.7.2) for `j = 0` from the Proposition on p.399,
  a uniqueness statement that assumes irreducible generic representations.
  This proof uses neither that Proposition, nor any functional equation, nor
  any gamma factor, and it keeps the full Whittaker-type scope.
- Derived rather than literal. The phrase "except for finitely many `q^{-s}`"
  becomes the single finite set `E` of spectral values of Step 2, chosen
  before `s` and built from the normalized generators of the two analytic
  premises. The dual part is pulled back under `s ↦ 1-s`, which on spectral
  points is `x ↦ q⁻¹/x`. Off `E`, the forms are the direct, unnormalized
  evaluations of the unique continuations of the actual integrals. Bilinearity
  comes from linearity of the actual integrals on common convergent
  half-planes together with uniqueness of rational continuations. JPSS gives
  no change-of-variables proofs of (2.11.2) and (2.11.4) at this point. Step 4
  supplies them for the supplied measures; compare the analogous computations
  in §2.10, pp.395–397.

Errata. The current registration of `jpss-1983-rankin-selberg` in
`/home/taskhub/pilot/literature/_central-library-pointers.md` has no erratum
pointer. The central library has no erratum file for the 1983 paper. The
Library and project note locations, including the audit note
`notes/audits/external-library-2026-10-22/whittaker-rankin-selberg.md`, record
no JPSS 1983 erratum. No registered erratum to JPSS 1983 was found. The
registered Jacquet 2012 correction (`jacquet-2012-conductor-correction`)
concerns only the 1981 conductor paper. The reading of pp.398–399 found no
misprint in (2.11.1)–(2.11.4).
