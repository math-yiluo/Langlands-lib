# Assembly of the rank-one extension span comparison

Module `Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonAssembly`.

This module derives `RankOneExtensionSpanComparisonStatement` from two other published
propositions, `LowerBlockQuotientDisintegrationStatement` and
`RankOneExtensionLowerJacquetFunctionalStatement`. Both enter as hypotheses `hdis` and `hJ`.
The main results are `rankOneExtensionSpanComparison_pointwise` and
`rankOneExtensionSpanComparison_of_statements`. The module does not prove either hypothesis,
so it does not prove the statement unconditionally.

The change of variables is the abstract theorem `rankOneExtensionUnfoldingCore` of
[RankOneExtensionSpanComparisonCore](RankOneExtensionSpanComparisonCore.md). This module
checks the hypotheses of that theorem for the concrete function

`H(z) = W₁(ι z) c_f(z) |det z|^(s - (k+1)/2)` on `GL_(1+(t+1))(F)`.

Here `W₁` is the scalar cutoff of the Whittaker function `W₀` and `c_f` is the scalar
coefficient of a compact lower section `f`.

## Provenance

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*,
Amer. J. Math. 105 (1983), Lemma (5.5), printed pp. 423–427. It is registered as
`jpss-1983-rankin-selberg`. In the source, `W` is replaced by a Whittaker function cut off
in the scalar `a`. A section `f` of the induced representation is chosen with support in
the open cell `Q · u(y)`, and the Whittaker functional of the induced representation is
written as an absolutely convergent integral. The source then unfolds the integral over
`N_(t+2) \ GL_(t+2)` through the open cell, and finds that the induced integral is a
nonzero constant times the base integral (formulas (4)–(9), pp. 424–426). This module
assembles the same computation from the published scalar cutoff
(`rankOneExtensionScalarCutoff`), the compact section (`rankOneExtensionCompactSection`),
the two hypotheses above and the core theorem. The interface, the choice `O = univ` in the
cutoff and section statements, and the constant `C ρ(U')` are choices of this
formalization; they are not quoted from the paper.

## Notation

- `B(g, x, a) = [g, 0; x, a]` (`rankOneExtensionLowerBlock`) and
  `u(y) = [I, y; 0, 1]` (`rankOneExtensionUpperCell`), both in `GL_(1+(t+1))`.
- `ι = rankInclusion (k + 1) : GL_(1+(t+1)) → GL_((1+(t+1))+k+1)`.
- `|·|` is `normalizedAbsoluteValue F.canonicalTopologicalData`, and
  `determinantWeight abv g s = |det g|^s`.
- `B⁻_1 = lowerTriangularSubgroup 1 F`; `lowerScalarEntry h` is the entry of `h ∈ B⁻_1`.
- `N_(t+1) = upperUnipotent (t + 1) F`; `θ` is the standard character `standardCharacter`.
- `Ψ_base(s; W₀, W')` is the block-one integral `unequalRankIntegral … 1 k μbase
  (rectangularMeasure ν 1 (t+1))`. `Ψ_ind(s; W₁, W'')` is the block-zero integral
  `unequalRankIntegral … 0 k μind (rectangularMeasure ν 0 ((1+t)+1))`. Both are taken with
  the rank casts `rankCastWhittaker`.

## Contents

Integrand (`section Integrand`), for any field `K` with an absolute value:

- `determinantWeight_mul_of_det_eq_one`: `|det(g h)|^s = |det h|^s` if `det g = 1`.
- `rankOneExtensionUnfoldingFunction ψ abv W c s` is the function
  `z ↦ W(ι z) c(z) |det z|^s` on `GL_(1+(t+1))(K)`. Here `W` is a Whittaker function of
  rank `(1+(t+1))+k` and `c` is any complex function.
- `rankOneExtensionUnfoldingFunction_lowerBlock_mul`: suppose
  `c(B(n, 0, 1) z) = θ(n)⁻¹ c(z)` for `n ∈ N_(t+1)`. Then `H(B(n, 0, 1) z) = H(z)`. The
  Whittaker factor contributes `θ(n)` (`whittaker_rankInclusion_lowerBlock_mul`), and
  `det B(n, 0, 1) = 1`.
- `rankOneExtensionUnfoldingFunction_upperCell_mul`:
  `H(u(y) z) = (W(ι z) |det z|^s) · (c(u(y) z) ψ(y_t))`. This uses
  `whittaker_rankInclusion_upperCell_mul` and `det u(y) = 1`.

Jacquet (`section Jacquet`):

- `mul_eq_integral_of_integrable_mul`: suppose `V = ∫ S` whenever `S` is integrable. Then
  `A V = ∫ A S` whenever `A S` is integrable. If `A = 0` both sides vanish. Otherwise `S`
  is integrable.

Measures (`section Measures`):

- `nullSingletonClass_of_map_mul`: let `K` be a field with a Hausdorff topological ring
  structure and its Borel σ-algebra. Let `ν` be an additively left-invariant measure on `K`,
  finite on compact sets. Suppose that for some `a ≠ 0`, the
  map `x ↦ a x` sends `ν` to `χ(a)⁻¹ • ν` with `χ(a) ≠ 1`. Then `ν` has no atoms. The point
  `0` is null because `ν{0} = χ(a)⁻¹ ν{0}` and `ν{0}` is finite. Every other point is a
  translate of `0`.

Scalar lower group (`section ScalarLower`):

- `continuous_rankOneExtensionScalarLower`: `a ↦ [a]` from `Kˣ` to `B⁻_1` is continuous.
- `lowerScalarEntry_one`: the entry of `1 ∈ B⁻_1` is `1`.
- `isCompact_preimage_lowerScalarEntry`: for a topological division ring `K`, the set of
  `h ∈ B⁻_1` whose entry lies in a compact set `U ∌ 0` is compact. It is the image of the
  compact set `{a ∈ Kˣ : a ∈ U}` under `a ↦ [a]`.

Weights (`section Weights`):

- `determinantWeight_lowerBlock_mul_upperCell`: if `|a| = 1`, then
  `|det(B(m, x, a) u(y))|^s = |det m|^s`.
- `sqrt_inv_mul_cpow`: `(√D)⁻¹ · D^z = D^(z - 1/2)` for real `D > 0`.

Smooth (`section Smooth`):

- `continuous_dual_apply_of_isSmooth`: for a smooth representation `ρ` of a topological
  group, a linear functional `Λ` and a vector `v`, the function `g ↦ Λ(ρ(g) v)` is
  continuous. It is locally constant by `matrixCoefficient_isLocallyConstant`.

p-adic statements (`section Padic`), for a `p`-adic field `F` with its canonical
topology:

- `rankOneExtensionUnfoldingFunction_lowerBlock_mul_upperCell`: the product formula on the
  cells. Assume the following:
  - `f₁ = modelMap π ℓπ v₁`;
  - `f₁(ι B(m, x, a)) = χ(a)⁻¹ f₂(ι B(m, x, 1))` for `a ∈ U`, and `f₁(ι B(m, x, a)) = 0`
    for `a ∉ U`, where `|a| = 1` on `U`;
  - the lower section `sec` satisfies `sec(u(y)) = φ(y) · (w ⊗ 1)`;
  - `π(ι u(y)) v₁ = v₁` for `y` in the support of `φ`.

  Then, for `H` built from `f₁` and the lower section coefficient
  `c = rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ sec` at exponent
  `s - (0 + k + 1)/2`:

  `H(B(m, x, a) u(y)) = 1_U(a) · (f₂(ι B(m, x, 1)) ℓ(σ(m) w) |det m|^(s - (1+k+1)/2)) · φ(y)`.

  The coefficient formula `rankOneExtensionLowerSectionCoefficient_lowerBlock_mul` gives
  `c(B(m, x, a) u(y)) = (|det m| / |a|^(t+1))^(-1/2) χ(a) φ(y) ℓ(σ(m) w)`. For `a ∈ U` the
  factor `χ(a)` cancels `χ(a)⁻¹`. Also `|a| = 1`, and `sqrt_inv_mul_cpow` moves the factor
  `|det m|^(-1/2)` into the exponent. When `φ(y) ≠ 0`, invariance of `v₁` removes `u(y)`
  from `f₁`.
- `continuous_rankOneExtensionUnfoldingFunction_of_continuous`: for smooth `π` and continuous
  `c`, the function `H` is continuous. The Whittaker function is a matrix coefficient, `ι`
  is continuous (`rankInclusionContinuous`), and `z ↦ |det z|^s` is continuous because
  `|det z| > 0`.
- `continuous_rankOneExtensionUnfoldingFunction`: the special case
  `c = rankOneExtensionLowerSectionCoefficient …`. That coefficient is continuous because
  sections are locally constant (`Induction.eval_isLocallyConstant`).
- `continuous_rankOneExtensionLowerCoefficient`: for any functional `Λ` on the lower model
  and any section `f`, the function `g ↦ Λ(I(g) f)` is continuous. The lower model is
  smooth (`isSmooth_normalizedOppositeParabolicInduced`), and the proof applies
  `continuous_dual_apply_of_isSmooth` to it.

Zero rows (`section ZeroRows`):

- `integral_dirac_of_subsingleton`: on a subsingleton space, `∫ f d(dirac a) = f a`.

## The pointwise theorem

`rankOneExtensionSpanComparison_pointwise hdis hJ` has the hypotheses and conclusion of the
premise of `rankOneExtensionSpanComparison_of_pointwise` in
[RankOneExtensionSpanTransfer](RankOneExtensionSpanTransfer.md). It assumes the following:

- `r = t + (1 + k + 1)` and `r = (1 + t) + (0 + k + 1)`;
- `π` and `σ₁` are smooth;
- the unipotent Haar measures in ranks `t + 1` and `(1 + t) + 1` are right invariant;
- `μbase` and `μind` are compatible quotient measures.

Let `W₀ ∈ whittakerSet ψ r π` and `W' ∈ inverseWhittakerSet ψ t σ₁`, and suppose that
`Ψ_base(s; W₀, W')` converges absolutely for `Re s > a₀`. The theorem produces
`W₁ ∈ whittakerSet ψ r π`, an inverse Whittaker function
`W'' ∈ inverseWhittakerSet ψ (1 + t) (rankOneExtensionLowerInduced F t χlift σ₁)` and a
constant `c ≠ 0`. For `Re s > a₀`, the integral `Ψ_ind(s; W₁, W'')` converges absolutely and

`Ψ_ind(s; W₁, W'') = c · Ψ_base(s; W₀, W')`.

The proof runs as follows.

1. Write `r = (1 + (t + 1)) + k`. Choose a functional `ℓπ` with `W₀ ∈ coefficientModel π ℓπ`
   and a functional `ℓ` with `W' ∈ coefficientModel σ₁ ℓ`. By `modelMap_surjective`, write
   `W'(g) = ℓ(σ₁(g) w)`.
2. The scalar cutoff `rankOneExtensionScalarCutoff`, with `f₂ = W₀` and `O = univ`, gives a
   compact open `U ∋ 1` with `0 ∉ U` and `|a| = 1` on `U`. It also gives
   `f₁ ∈ coefficientModel π ℓπ` with the formulas `hin` and `hout` above. Take
   `W₁ = f₁` and `f₁ = modelMap π ℓπ v₁`.
3. The compact section `rankOneExtensionCompactSection`, for `v₁`, `w` and `O = univ`, gives
   an integrable `φ` with `∫ φ = 1` and a lower section `sec` with `sec(u(y)) = φ(y)(w ⊗ 1)`.
   Moreover `v₁` is fixed by `ι u(y)` for `y` in the support of `φ`.
4. `hJ` gives the functional `Λ ∈ glInverseFunctionals ψ (1 + t)` on the lower model. Set
   `W''(g) = Λ(I(g) sec)`, that is, `W'' = coefficientMap M Λ (M.asModuleEquiv sec)`. It lies
   in the inverse Whittaker set by construction, and it is continuous
   (`continuous_rankOneExtensionLowerCoefficient`).
5. The adapter `rankOneExtensionDisintegration_of_statement hdis` of
   [RankOneExtensionDisintegration](RankOneExtensionDisintegration.md) gives a
   right-invariant measure `ρ` on `B⁻_1`, positive on open sets and finite on compact sets.
   It also gives a constant `C > 0` and the chart transfer for Borel measurable functions
   on `N_((1+t)+1) \ GL_((1+t)+1)`. Let `U' = {h ∈ B⁻_1 : lowerScalarEntry h ∈ U}`. It is
   open and contains `1`, so `ρ(U') > 0`. It is compact, so `ρ(U') < ∞`. The constant is
   `c = C · ρ(U') ≠ 0`.
6. The core theorem is applied with the following data:
   - `μ = μbase` (right invariant by `IsCompatible.right_invariant`);
   - `dx = rectangularMeasure ν 1 (t+1)`, the measure `ρ`, and `ν = ν.val.measure`;
   - `χ = T.normalizedAbsHom`, with scaling `padicScalarHaarScaling`;
   - `D = lowerBlockQuotientDensity T (t+1) 1`, which equals `|det g|⁻¹` on `[g]`;
   - `chart = rankOneExtensionQuotientChart`, `μ₂ = μind`, `fQ` the block-zero integrand
     and `fB` the block-one integrand;
   - the function `H` above, the function `φ`, and the set `U'`.

   `ν` has no atoms by `nullSingletonClass_of_map_mul` at the uniformizer, whose absolute
   value is `q⁻¹ ≠ 1`. The hypotheses of the core theorem are checked as follows:
   - `htr`: `fQ` is continuous, hence Borel measurable, so the adapter's transfer applies.
   - `hH`: from `rankOneExtensionUnfoldingFunction_lowerBlock_mul` and
     `rankOneExtensionLowerSectionCoefficient_unipotent_mul`.
   - `hWc`: from the cell formula, with `1_U(lowerScalarEntry h) = 1_U'(h)`.
   - `hJ`: by `rankOneExtensionQuotientChart_mk`, the value `fQ(chart([g], (x, h)))` equals
     `W₁(ι B) W''(B) |det B|^(s - (k+1)/2)` for `B = B(g, x, [h])`. By
     `rankOneExtensionUnfoldingFunction_upperCell_mul`,
     `H(u(y) B) = (W₁(ι B) |det B|^(s - (k+1)/2)) · S(y)`, where `S` is the scalar
     integrand `rankOneExtensionStableIntegrand … sec B`. The Jacquet formula from `hJ`
     says `W''(B) = ∫ S` whenever `S` is integrable. Then
     `mul_eq_integral_of_integrable_mul` gives the required identity.
   - `fB` is integrable by the convergence hypothesis.
7. The core theorem gives integrability of `fQ` for `μind` and
   `∫ fQ dμind = C ρ(U') (∫ φ) ∫ fB`, with `∫ φ = 1`. The block-zero rectangular measure is
   `dirac 0` (`rectangularMeasure_zero_rows`) on a subsingleton matrix space. Hence
   convergence of `Ψ_ind` is integrability of `fQ`, and `Ψ_ind = ∫ fQ dμind` by
   `integral_dirac_of_subsingleton`. Finally, `Ψ_base = ∫ fB` by `integral_prod`.

## The conditional theorem

`rankOneExtensionSpanComparison_of_statements hdis hJ :
RankOneExtensionSpanComparisonStatement`. The proof introduces the data of the statement and
applies `rankOneExtensionSpanComparison_of_pointwise` with `k = r - t - 2`. The statement
fixes the rank equalities `hrBase` and `hrInd` at this `k`. The premise is the pointwise
theorem. `IsOfWhittakerType` begins with `IsAdmissible`, which begins with `IsSmooth`, so
`hπ.1.1` and `hσ.1.1` give smoothness of `π` and `σ₁`.
