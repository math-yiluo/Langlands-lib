# Reduction of the weighted Whittaker square estimate

Author: Worker 724. The proof reuses `normalizedAbs_prod`,
`diagonal_abs_last` and `diagonal_abs_bound` from
`Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`, written
by Worker 676. These helpers are public with their existing statements and proofs.

## What this module proves

The main theorem is the conditional theorem

```lean
theorem weightedWhittakerSquare_of
    (h1 : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (m : ℕ), RecursiveQuotientIntegrationStatement F T m)
    (h2 : SquareIntegrableWhittakerRestrictionStatement.{uF, uV}) :
    WeightedWhittakerSquareStatement.{uF, uV}
```

Its conclusion is the published proposition
`Langlands.RankinSelberg.WeightedWhittakerSquareStatement.{uF,uV}` for both
character signs, for every positive rank including rank one, and with both
universes `uF` and `uV`. It has two hypotheses. Both are published statement
definitions of the Library.

- `h1` is the recursive quotient integration formula
  `RecursiveQuotientIntegrationStatement` in every rank, at all `p`, `F`, `T`.
  This is JPSS printed p. 449, formula (1). The Library proves it as
  `recursiveQuotientIntegration` in module
  `Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof`.
- `h2` is the restricted Whittaker square estimate
  `SquareIntegrableWhittakerRestrictionStatement`. Only its case `k = 0` is
  used. This is JPSS printed p. 449, formula (2). The Library proves it as
  `squareIntegrableWhittakerRestriction` in module
  `Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionProof`.

This module does not import those proofs, and it does not prove the target on
its own. It proves only the implication. The final module
`Langlands.Representation.RankinSelberg.WeightedWhittakerSquareProof`
discharges `h1` and `h2` with the two published proofs.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source and implemented route

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105** (1983),
367–464, Section 8.3, printed pp. 448–451 (registered source
`jpss-1983-rankin-selberg`). The weighted square is the second Cauchy–Schwarz
factor on printed p. 451, which the source calls finite "by the previous case".
The previous case is the equal-rank argument on printed p. 449. The statement
Markdown `WeightedWhittakerSquareStatement.md` explains this specialization.

Write `W = f.val`, and let `r = n + 1` be the rank. The integrand on the coset of
`x ∈ GL_r(F)` is

\[
 |W(x)|^2\,|\Phi(e_r x)|^2\,|\det x|^{2a}, \qquad a > 0 .
\]

The source route has three steps. First, formula (1) integrates over
`(N_(r-1) \ G_(r-1)) × F^× × K_r` with `x = diag(g,1) · t · k` and weight
`|det g|⁻¹`. Second, the corank-one estimate (2) bounds
`∫ |W[diag(g,1)]|² |det g|⁻¹ dg`. Third, the source splits off the region
`|det g| ≥ 1` and bounds it by gauges.

The implemented proof follows the first two steps. It replaces the gauge step
by a support bound: a smooth Whittaker function `W` vanishes at `diag(g,1)`
when `|det g|` is large (`exists_normalizedAbs_det_bound`). Then
`|det g|^(2a) ≤ max(C,1)^(2a)` on the support, and the whole restricted
integral is bounded by (2) alone. No gauge estimate is used.

The rank-one case does not use (1) or (2). There `N_1` is trivial, every
element is central, `|W|` is constant, and the integral reduces to a geometric
tail over determinant slices.

The inverse character sign is reduced to the standard sign for the additive
character `x ↦ ψ(-x)`.

## Sections and declarations

### `ShellTail`

`lintegral_indicator_zpow_ord_ne_top` is a measure-theoretic tail lemma. Let
`μ` be a measure on `X` and `ord : X → ℤ` a function with measurable fibres
`S_j = {ord = j}`. Let `τ` be a measure-preserving map with
`ord (τ x) = ord x + 1`, and assume `μ(S_0) < ∞`. Then for `0 < ρ < 1` and every
integer `N`,

\[
 \int^{-} \mathbf 1_{\{N \le \mathrm{ord}\}}\,\rho^{\mathrm{ord}}\,d\mu < \infty .
\]

Proof. Since `τ⁻¹ S_(j+1) = S_j`, all fibres have the mass of `S_0`, by
induction over `ℤ`. The set `{N ≤ ord}` is the disjoint union of the fibres
`S_(N+j)` with `j ∈ ℕ`. On `S_(N+j)` the integrand is the constant
`ρ^N ρ^j`. The integral is therefore `ρ^N μ(S_0) Σ_j ρ^j = ρ^N μ(S_0)/(1-ρ)`,
which is finite.

### `ProductBound`

`lintegral_map_withDensity_prod_ne_top` bounds a lower integral against a
pushforward `c_*((μs × (dA × dB)).withDensity w)`. Assume that `w` is
measurable and `c` is almost-everywhere measurable. Assume a set `S` of full
`dB`-measure and functions `P`, `Q` with
`w(x,a,b) · h(c(x,a,b)) ≤ P(x) Q(a)` for `b ∈ S`. Assume `P` is finite-valued,
`∫ P dμs < ∞`, `∫ Q dA < ∞` and `dB` is finite. Then `∫ h d(c_* …) < ∞`.

The proof chains `lintegral_map_le`, `lintegral_withDensity_le_lintegral_mul`
and two applications of the Tonelli inequality `lintegral_prod_le`. These
inequalities need no measurability of the integrand. The result is at most
`(∫ P dμs) · (∫ Q dA) · dB(univ)`.

### `LocalFieldFacts`

Here `|·|` is `T.normalizedAbs`, `q` is the residue cardinality and `ord` is
`T.ord`, so `|x| = q^(-ord x)` for `x ≠ 0`.

- `normalizedAbs_rpow_eq_zpow_ord`: `|x|^s = (q^(-s))^(ord x)` for `x ≠ 0`.
- `residueCardinality_rpow_neg_mem`: `0 < q^(-s) < 1` when `s > 0`.
- `exists_ord_lower_bound`: for every real `R` there is an integer `N` with
  `N ≤ ord x` whenever `x ≠ 0` and `|x| ≤ R`.
- `ord_eq_zero_iff_mem_integralUnits_of_units`: a unit has order zero exactly
  when it lies in `integralUnits T.Integers`.
- `normalizedAbs_det_of_mem_integralSubgroup`, imported from the shared
  `IntegralDeterminant` module: `|det k| = 1` for `k` in the
  integral subgroup. Both `det k` and `det k⁻¹` are integral, and their product
  is one.
- `continuous_normalizedAbs'`: `T.normalizedAbs` is continuous for
  `T.topology`.
- `nonempty_unitaryCentralCharacter_of_isSquareIntegrable`: `T.IsSquareIntegrable ρ`
  gives a unitary central character. A Borel Haar measure on the central
  quotient exists by `T.exists_isHaarMeasure_centralQuotient`. The predicate at
  this measure contains a `UnitaryCentralCharacter ρ`.
- `lintegral_units_indicator_zpow_ord_ne_top`: the multiplicative tail
  `∫ 1_{N ≤ ord t} ρ^(ord t) d^×t` is finite for `localMultiplicativeHaar`,
  for every Borel measurable structure on `F^×`. This is the `ShellTail`
  lemma with `τ` the left multiplication by the uniformizer unit
  `LocalFactor.PadicAbelian.uniformizerUnit T`, of order one. Left
  multiplication preserves the Haar measure. The order-zero fibre is
  `O^×`, of mass one by `localMultiplicativeHaar_integerUnits`. The fibres are
  measurable because `ord` is continuous on units (`continuous_ord_units`) with
  values in the discrete space `ℤ`.

### `Continuity`

`continuous_weightedSquareIntegrand` states that the integrand of the target
is continuous on `N_(n+1) \ GL_(n+1)(F)` for a smooth representation and a
continuous absolute value. It holds for every field with a ring topology. Coefficient
functions of smooth vectors are locally constant
(`matrixCoefficient_isLocallyConstant`). The last row is continuous, `Φ` is
locally constant, and `abv (det x)` is continuous and positive. The function
descends through the open quotient map `leftQuotient_isOpenQuotientMap`. The
proofs use this lemma for the almost-everywhere strong measurability part of
`Integrable`.

### `StandardWeightedSquareAt`

`StandardWeightedSquareAt F T n` is an internal proposition definition. It is
the standard-character clause of `WeightedWhittakerSquareStatement` at fixed
`p`, `F`, `T` and `n`. It has the published statement's installed instances
and binders in the same order. These are the topology, valuation and
local-field structure of `T`, Borel structures on `GL_(n+1)`, on its upper
unipotent subgroup and on the quotient, then `ψ`, the right-invariance
instance, the compatible measure `μ`, `V`, the irreducible square-integrable
`π`, and finally `ℓ`, `f`, `Φ` and `a > 0`. Its conclusion is the
integrability of the standard-character integrand displayed in the statement.
The proof of `weightedWhittakerSquare_of` uses it as the first conjunct of the
published statement, and Lean checks the match.

### `RankOne`

- `norm_coefficientModel_rankOne`: in `GL_1` every element is central
  (`rankOne_mul_comm`). A unitary central character `c` therefore gives
  `|W(g)| = |c(g)| |W(1)| = |W(1)|` for every coefficient-model function.
- `mem_integralSubgroup_rankOne_of_ord_eq_zero`: a rank-one matrix whose
  determinant has order zero is integral with integral inverse. Its single entry
  is its determinant.
- `standardWeightedSquare_zero`: `StandardWeightedSquareAt F T 0`. Measurability
  comes from `Continuity`. The central character comes from square
  integrability. On the coset of `g`, the last row is the single entry `det g`.
  Let `M` bound `|Φ|`, and let `R` bound `|y|` on the compact support of `Φ`.
  Choose `N` with `N ≤ ord y` whenever `|y| ≤ R`. The integrand is at most

  \[
   |W(1)|^2 M^2\,\mathbf 1_{\{N \le \mathrm{ord}\det\}}\,\rho^{\mathrm{ord}\det},
   \qquad \rho = q^{-2a}.
  \]

  The integer order is `determinantOrder T 0` on the quotient, from
  `DeterminantSlices`, with measurable fibres `measurableSet_determinantSlice`.
  Right translation by the scalar `ϖ` raises it by one
  (`determinantOrder_rightTranslate`). It preserves `μ` by the right-invariance
  field of `IsCompatible`. The order-zero slice lies in the image of the
  compact group `GL_1(O)` (`isCompact_integralSubgroup`) under the continuous
  quotient map. Its `μ`-mass is finite because `μ` is regular (also a field of
  `IsCompatible`). The `ShellTail` lemma concludes.

### `DeterminantSupport`

- `normalizedAbs_prod`: `|∏ f i| = ∏ |f i|` over a finite set. Imported
  from Worker 676's Iwasawa support module.
- `diagonal_abs_last`: if `M` has last row `e_last` and
  `M = u · diag(a) · κ` with `u` upper unipotent and `κ` integral, then
  `|a_last| = 1`. Imported from the same module.
- `diagonal_abs_bound`: if `|a_last| = 1` and every adjacent ratio
  satisfies `|a_i / a_(i+1)| ≤ B` with `B ≥ 1`, then `|a_i| ≤ B^r` for all `i`.
  Imported from the same module.
- `exists_normalizedAbs_det_bound r`: for every smooth `π` of
  `GL_(r+1)(F)`, every `ℓ : glFunctionals ψ r π` and every
  `f : (coefficientModel π ℓ).toSubmodule`, there is a constant `C` with
  `|det x| ≤ C` whenever `x` has last row `e_last` and `f.val x ≠ 0`.
  Proof. Take the published Iwasawa decomposition `x = u · diag(ϖ^λ) · κ`
  (`exists_isUniformizingElement`, `exists_iwasawa`). The left
  `N`-equivariance of `f.val` makes `f.val (diag(ϖ^λ) κ) ≠ 0`. The published
  support theorem `Whittaker.smoothSimpleRootSupport` gives an `R` bounding all
  adjacent ratios. With `B = max 1 R`, the two imported lemmas give
  `|a_i| ≤ B^r`. Finally `det u = 1` and `|det κ| = 1`, so
  `|det x| = ∏ |a_i| ≤ (B^r)^(r+1)`.

### `HigherRank`

- `norm_matrixCoefficient_recursiveQuotientRepresentative`: write
  `diag(g,1) · t · k` for `recursiveQuotientRepresentative n g t k`. With a
  unitary central character, `|W_v(diag(g,1) · t · k)| = |W_(π(k)v)(diag(g,1))|`.
  The scalar commutes with `k`, the central character has absolute value one,
  and `matrixCoefficient_mul` moves `k` into the vector.
- `rankInclusion_one_lastRow`: the last row of `diag(g,1)` is `e_last`.
- `exists_finset_integralOrbit r`: for smooth `π`, the orbit
  `{π(k)v : k ∈ GL_(r+1)(O)}` is contained in a finite set. The orbit map is
  locally constant (`Hecke.orbitMap_locallyConstant`), and the integral
  subgroup is the compact level-zero subgroup (`levelSubgroup_zero`).
- `exists_ord_lower_bound_of_lastRow r Φ`: there is an `N` with `N ≤ ord t`
  whenever `k` is integral and `Φ(t · e_last k) ≠ 0`. Indeed
  `t = Σ_j (t k_(last,j)) (k⁻¹)_(j,last)`. The entries of `k⁻¹` are integral,
  so `|t| ≤ Σ_j |t k_(last,j)|`, which is bounded on the compact support of `Φ`.
- `standardWeightedSquare_succ m h1m h2`: `StandardWeightedSquareAt F T (m+1)`
  from `h1m : RecursiveQuotientIntegrationStatement F T m` and `h2`. The rank is
  `m + 2`.

  Proof. Second countability of `F`, `F^×`, both general linear groups and the
  smaller quotient is installed. Then the continuous coordinates
  `recursiveQuotientCoordinates m` are measurable for the product σ-algebra.
  Take `μs = unipotentQuotientHaar F m`, which is compatible
  (`unipotentQuotientHaar_isCompatible`). By `h1m`,
  `μ = coords_*((μs × (d^×t × dk)).withDensity |det g|⁻¹)`. Write `f` as
  `modelMap π ℓ v`. Let `S` be a finite set containing the integral orbit of
  `v`, and for each `w ∈ S` let `C_w` be the determinant bound of
  `exists_normalizedAbs_det_bound` for `modelMap π ℓ w`. Put
  `D_w = max(C_w,1)^(2a)` and

  \[
   P(g) = \sum_{w\in S} D_w\,|W_w(\mathrm{diag}(g,1))|^2\,|\det g|^{-1},
  \]

  where the summand without `D_w` is the integrand of `h2` at `k = 0` for
  `modelMap π ℓ w`. By `h2` at `n = m`, `k = 0` and the measure `μs`, each
  summand is integrable, so `P` is integrable. For `k ∈ K = GL_(m+2)(O)`, the
  representative has last row `t · e_last k` and
  `|det| = |det g| |t|^(m+2)` (`recursiveQuotientRepresentative_lastRow`,
  `recursiveQuotientRepresentative_det_abs`, `|det k| = 1`). Assume the
  integrand is nonzero. Then `N ≤ ord t`, and `W_(π(k)v)(diag(g,1)) ≠ 0`, so
  `|det g| ≤ C_(π(k)v)`. Hence

  \[
   |\det g|^{-1}\,|W|^2|\Phi|^2|\det|^{2a}
   \le P(g)\cdot M^2\,\mathbf 1_{\{N\le \mathrm{ord}\,t\}}\,\rho^{\mathrm{ord}\,t},
   \qquad \rho = q^{-2a(m+2)},
  \]

  where `M` bounds `|Φ|`. The `t`-factor is integrable by
  `lintegral_units_indicator_zpow_ord_ne_top`. The measure `dk` has total mass
  one (`generalLinearHaar_integralSubgroup`). `K` is open, so almost every point
  for `dk` lies in `K`. The density is measurable because `|det|` is continuous
  on the quotient. `lintegral_map_withDensity_prod_ne_top` concludes.

### `Assembly`

- `standardWeightedSquare_of T h1 h2 n`: case analysis on `n`. Rank one is
  `standardWeightedSquare_zero`, and rank `m + 2` is `standardWeightedSquare_succ`.
- `weightedWhittakerSquare_of h1 h2`: the standard clause is
  `standardWeightedSquare_of`. For the inverse clause, put
  `ψ' = ψ.scale (-1)`. By `standardCharacter_scale_neg_one`, the standard
  character of `ψ'` is the inverse standard character of `ψ`. An
  `ℓ : glInverseFunctionals ψ n π` is therefore the same linear functional as an
  `ℓ' : glFunctionals ψ' n π`, with the same coefficient map. Write
  `f = modelMap π ℓ v`. The inverse-character integrand for `(ψ, ℓ, f)` and the
  standard integrand for `(ψ', ℓ', modelMap π ℓ' v)` agree on every coset by
  definitional unfolding. `Integrable.congr` transfers the standard clause.

## Scope

Every binder of the target is kept. This covers every prime, every supplied
`T` (no canonical topology is assumed), every rank including rank one, every
compatible measure `μ`, every `ψ`, and zero functionals, vectors and
Schwartz–Bruhat functions. The only hypotheses beyond the target's binders are
`h1` and `h2`.
