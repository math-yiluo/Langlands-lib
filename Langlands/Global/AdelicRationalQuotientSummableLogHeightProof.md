# Summability of a power of the logarithmic height against conjugation counts

Module `Langlands.Global.AdelicRationalQuotientSummableLogHeightProof`. It proves

```lean
theorem Langlands.Global.rationalQuotientSummableLogHeight :
    RationalQuotientSummableLogHeightStatement
```

The statement `Langlands.Global.RationalQuotientSummableLogHeightStatement` is in the module
`Langlands.Global.AdelicTemperedComponentInputs`, whose Markdown explains it. The theorem has no
hypotheses beyond those of the statement. It uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Let `F` be a number field and let `G` be a connected reductive group over `F` (affine, locally
of finite type). Let `rho : MatrixRepresentation G (Fin N)` be a closed matrix embedding. Write
`Γ = G(F) = rationalSubgroup F G`, `[G] = RationalQuotient F G` and
`σ_{[G]} = rationalLogHeight F G rho`. The measure `μG` on `[G]` is
`LeftCosetSpace.discreteQuotientMeasure Γ (isDiscrete_rationalSubgroup F G) Measure.haar`.
There is `m : ℕ` such that for every compact `C ⊆ G(𝔸)`

`∫⁻ y, #{q ∈ Γ : y.out⁻¹ q y.out ∈ C} · ENNReal.ofReal ((σ_{[G]}(y)^(2m))⁻¹) ∂μG < ∞`.

The statement also supplies a maximal compact subgroup `K` and a minimal parabolic `P₀` with
`IsIwasawaCompact p₀ K`. The proof does not use them: it chooses its own Siegel data. For
`N > 0` the exponent is `m = |I| + |Δ|`. Here `I` indexes a splitting of the split central torus
of the chosen Siegel setup, and `Δ` is its set of simple relative roots. For `N = 0` it is
`m = 0`.

## Declarations

In the namespace `Langlands.Global.AdelicSiegelFactors`:

- `inv_mul_mul_eq_conj_mul`: in a group, if `z` commutes with every element and `x` commutes
  with `m`, then `(z x)⁻¹ (n m) = (x⁻¹ n x) m (z x)⁻¹`.
- `adelicHeight_mul_five_le`: if `N > 0` and `‖g_k‖ ≤ b_k` for `k = 1, …, 5`, then
  `‖g₁ g₂ g₃ g₄ g₅‖ ≤ b₁ b₂ b₃ b₄ b₅`. Here `‖·‖ = RepresentationGrowth.adelicHeight F G rho`.
- `adelicLogHeight_sub_log_le_rationalLogHeight`: let `N > 0`, `L ≥ 1`, `X ∈ G(𝔸)` and
  `z ∈ [G]`. If `‖X‖ ≤ L ‖q z.out‖` for every `q ∈ Γ`, then
  `σ(X) - log L ≤ σ_{[G]}(z)`, where `σ = adelicLogHeight F G rho`.
- `exists_siegelTranslateCover` (for `N > 0`): there are a countable type `Idx`, points
  `y : Idx → G(𝔸)`, a real `R`, an exponent `m` and weights `Φ : Idx → ℝ≥0∞` with
  `∑ Φ < ∞`. Every `z ∈ [G]` has an index `κ`, some `g₀ ∈ Γ` and some `d` with `‖d‖ ≤ R`
  (`d ∈ adelicHeightSublevel F G rho R`) such that `z.out = g₀ y_κ d` and
  `ENNReal.ofReal ((σ_{[G]}(z)^(2m))⁻¹) ≤ Φ κ`. The weight bound holds for `z` and the index
  that the proof assigns to `z`, not for every coset in the image of `y_κ D`.
- `rationalQuotientSummableLogHeight_of_pos`: the conclusion of the statement for `N > 0`.
- `rationalQuotientSummableLogHeight_of_zero`: the conclusion of the statement for `N = 0`.

In the namespace `Langlands.Global`: `rationalQuotientSummableLogHeight`, the statement, by
the two cases.

## Proof

### The unfolding step

Let `D = adelicHeightSublevel F G rho R`. It is compact (`isCompact_adelicHeightSublevel`; it
uses that `rho` is closed), so `D C` is compact. The published
`LeftCosetSpace.lintegral_conjugationCount_mul_le` (module
`Langlands.Global.LeftCosetConjugationCount`) applies with the family `y`, the set `D`, the
weight `w(z) = ENNReal.ofReal ((σ_{[G]}(z)^(2m))⁻¹)` and the weights `Φ`. Its hypothesis is the
conclusion of `exists_siegelTranslateCover`. Its integrand is the integrand of the statement.
It bounds the integral by `(∑ Φ) · haar(D C)`, a product of two finite numbers. This proves
`rationalQuotientSummableLogHeight_of_pos`.

### The Siegel data

The proof of `exists_siegelTranslateCover` takes the same data as the published proof of
`SiegelDominatedIntegrabilityStatement` (`siegelDominatedIntegrability_of_pos`, module
`Langlands.Global.AdelicSiegelDominatedIntegrabilityProof`):

- the algebraic Siegel setup `(T, i, ν, T₀, j)` of `siegelAlgebraicSetupExistence_of_structural`;
- a compact subgroup `K'`, a finite set `W ⊆ G(𝔸)¹` and compact factors `C'` with compact
  subgroup `K'` and a threshold `t`, from `exists_compact_openSubgroup_finite_cover` and
  `exists_rational_mul_mem_weakSiegelProduct_mul`;
- the split central torus `zc : Z₀ → T` of the setup, a splitting `Z₀ ≅ 𝔾_m^I`, and rational
  characters `χ_k` of `G` from `RepresentationGrowth.exists_characterNorm_full`;
- the coordinates `λ = siegelCoordinates zc χ` of `A_{Z₀} × A_{T₀}`: `|χ_k(z)|` for `k ∈ I` and
  `|α(x)|` for simple relative roots `α ∈ Δ`. The integer dyadic index is
  `κ = SiegelSetMeasure.zIndex λ`, `κ_c = ⌊log₂ λ_c⌋`.

Write `a = siegelTorusMap zc : A_{Z₀} × A_{T₀} → G(𝔸)`, `(z, x) ↦ z x`. By
`exists_rational_mul_mem_centralSiegelSet_mul`, every `g ∈ G(𝔸)` has `r ∈ Γ` with
`r g = n m a(p) k w`. Here `n` is in the image of `C'.omegaN`, `m` in the image of
`C'.omegaM`, `p = (p₁, p₂)` with `p₂` in the chamber `|α(p₂)| ≥ t`, `k ∈ K'` and `w ∈ W`.

### The family and the bound on `d`

The index type is `Idx = (I ⊕ Δ → ℤ)`. For each `κ` that is the dyadic index of some `p` with
`p₂` in the chamber, choose such a point `p_κ`. For the other `κ` put `p_κ = 1`. Put
`y_κ = a(p_κ)`. These other indices are never assigned to a coset below. They enter only
through their terms `Φ_κ` in the sum of majorants, which is still finite.

Every coset is assigned one index, the dyadic index of its own Siegel representative. All bounds
below concern a coset and its assigned index. They are not bounds on the whole image of `y_κ D`
in `[G]`. For instance, if `Δ` is nonempty, the chamber condition `|α(p₂)| ≥ t` bounds the
coordinate `κ_α` of a realized index from below. So infinitely many indices are unrealized, and
for all of them `y_κ D = D`. A coset in the image of `D` has a fixed height, while the bounds
`max(1, c₀ ∑_c |κ_c| - C₀)` for these indices are unbounded.

Let `z ∈ [G]`. Apply the cover to `z.out` and let `κ` be the dyadic index of the resulting `p`.
Put `X = r z.out` and `d = y_κ⁻¹ X`, so that `z.out = r⁻¹ y_κ d`. Write `a(p_κ) = z' x'` with
`z' = positiveMap Z₀ (p_κ)₁` central (`positiveMap_central`). The Levi factor commutes with `x'`
(`positiveMap_commute_of_mem_standardLevi` and the setup clause
`standardLevi = torusCentralizer`). The group identity `inv_mul_mul_eq_conj_mul` gives

`d = (x'⁻¹ n x') · m · a(p_κ⁻¹ p) · k · w`.

The five factors have bounded heights:

- `‖x'⁻¹ n x'‖ ≤ B_N` by `exists_adelicHeight_conj_unipotent_le`, since `(p_κ)₂` lies in the
  chamber;
- `‖m‖` is bounded on the compact image of `C'.omegaM`;
- `p_κ⁻¹ p` lies in the compact dyadic box `{1/2 ≤ λ_c ≤ 2}`
  (`SiegelSetMeasure.inv_mul_mem_dyadicBox_of_zIndex_eq` and
  `isCompact_dyadicBox_siegelCoordinates`), and `‖a(·)‖` is bounded there;
- `‖k‖` is bounded on the compact `K'` and `‖w‖` on the finite `W`.

With `R` the product of the five bounds (each at least `1`), `adelicHeight_mul_five_le` gives
`‖d‖ ≤ R`.

### The lower bound of `σ_{[G]}`

Keep `z`, its Siegel representative `X = r z.out` and its index `κ`. The point `y_κ` is the
image under `i` of the positive point `zc((p_κ)₁) · j((p_κ)₂)` of `T` (`PositiveRealTorus.map_intrinsicSubgroup_le`). The published
diagonal height inequality `exists_adelicHeight_map_le_rational_mul` (module
`Langlands.Global.AdelicSiegelDiagonalHeightBound`), for the split torus `T` and `f = i`, gives
`c_A` with `‖y_κ‖ ≤ c_A ‖ρ y_κ‖` for every rational `ρ`. For `q ∈ Γ` put `ρ = q r⁻¹`. Then
`q z.out = ρ y_κ d`. Submultiplicativity and `‖d⁻¹‖ = ‖d‖ ≤ R` (`adelicHeight_inv`) give

`‖X‖ ≤ ‖y_κ‖ R ≤ max(c_A, 1) ‖ρ y_κ‖ R ≤ max(c_A, 1) R² ‖q z.out‖`.

With `L = max(c_A, 1) R²`, `adelicLogHeight_sub_log_le_rationalLogHeight` gives
`σ(X) - log L ≤ σ_{[G]}(z)`. Its proof uses `‖·‖ = N^{[F:ℚ]} · adelicSourceNorm`
(`adelicHeight_eq_scalar_mul_sourceNorm`). It bounds the infimum in the definition of
`rationalLogHeight` from below (`le_ciInf`), then takes logarithms.

The point `X` is a point of the Siegel set with torus coordinate `p`. So the published
`exists_abs_zIndex_le` gives `A ≥ 0` and `B` with `|κ_c| ≤ A σ(X) + B` for every coordinate
`c`. Hence `|κ_c| ≤ A σ_{[G]}(z) + B'` with `B' = A log L + B`. Summing over the
`n = |I| + |Δ|` coordinates and applying the published `max_le_of_sum_le` gives

`max(1, c₀ ∑_c |κ_c| - C₀) ≤ σ_{[G]}(z)`, with `c₀ = 1/((n + 1)(A + 1))` and
`C₀ = |B'|/(A + 1)`.

Take `m = n` and `Φ κ = ENNReal.ofReal (max(1, c₀ ∑_c |κ_c| - C₀)^{-2n})`. Then
`σ_{[G]}(z)^{-2m} ≤ Φ κ`, and `∑_κ Φ κ < ∞` by `SiegelSetMeasure.tsum_decay_ne_top`.

### The case `N = 0`

A closed embedding into `GL_0` makes `G(𝔸)` a subsingleton
(`RepresentationGrowth.isClosedEmbedding_adelicMatrix`), hence compact. With `m = 0` the
weight is `1`. `lintegral_conjugationCount_mul_le` applies with the one-point family `1`, `D` the
whole space and `Φ = 1`. It bounds the integral by `haar(G(𝔸) · C) < ∞`.

## Provenance

The statement is derived from J. Bernstein, *On the support of Plancherel measure*, J. Geom.
Phys. 5 (1988), 663–710 (`bernstein-1988-support-plancherel`), §§3.2–3.4, and from P. Delorme,
*On the spectral theorem of Langlands*, Adv. Math. 426 (2023), 109107
(`delorme-2023-spectral-theorem-langlands`), (2.10) and Remark 3.4. The Markdown of the
statement explains this derivation.

The argument is analogous to Bernstein's summable weights (§3.2, pp. 681–683). There a net is
a subset `𝒩 ⊆ X` with a covering ball, that is, a ball `B` with `B · 𝒩 = X`. A weight `w` is
summable if `∑_{n ∈ 𝒩} w(n)⁻¹ < ∞` for some countable net `𝒩`, a sum of reciprocal weights
evaluated at the points of the net. A net `𝒩` is sparse if, for every ball `Ω` in the acting
group, the number of points of `𝒩 ∩ Ω x` is bounded by a constant `k(𝒩, Ω)` independent of
`x ∈ X` (§3.2, p. 682). For a sparse net, summability is equivalent to
finiteness of the sum on that net (§3.2, Criterion, pp. 682–683). Bernstein compares the sum
on a sparse net with the integral of `w⁻¹` against his standard measure, which shows that `w`
is summable if and only if this integral is finite (§3.3, Criterion, p. 685). Here the weight
is `σ_{[G]}^{2m}`. The images of the translates `y_κ D` cover `[G]`, but `∑_κ Φ_κ` is a sum of
dyadic upper bounds, not a sum over a net. Each `Φ_κ` bounds `σ_{[G]}^{-2m}` on the cosets
assigned to `κ`. It is not the reciprocal weight at the center `y_κ`, and the family uses the
center `1` for each unrealized index (infinitely many when `Δ` is nonempty). The module
`Langlands.Global.LeftCosetConjugationCount` bounds the integral of the conjugation count
against `σ_{[G]}^{-2m}` directly by unfolding, with the bound `(∑_κ Φ_κ) · haar(D C)`. It does
not use the standard measure.

The count is related to the standard measure as explained in the Markdown of
`RationalQuotientSummableLogHeightStatement` (module
`Langlands.Global.AdelicTemperedComponentInputs`). For a compact identity neighbourhood `B` and
each compact `C`, the count is at most a constant times the reciprocal volume `μG([x B])⁻¹` of
the image of a ball. For `C = BB⁻¹` the count and this reciprocal volume are comparable in both
directions. Delorme puts `Ξ^{[G]}(x) = (vol_{[G]} x B)^{-1/2}` (p. 8, at (2.9)), so
`(Ξ^{[G]})²` is this reciprocal quotient-ball volume. In Remark 3.4 (pp. 11–12) it is the
density of Bernstein's standard measure.

The geometric inputs are reduction theory for `G(F) \ G(𝔸)`:

- the Siegel cover of `G(𝔸)`, and the upper bound `|κ_c| ≤ A σ(X) + B` of the absolute dyadic
  coordinates of a Siegel point `X` by its logarithmic height (`exists_abs_zIndex_le`), both from
  `Langlands.Global.AdelicSiegelDominatedIntegrabilityProof`;
- the norm minimality of positive torus points among their rational translates (Mœglin and
  Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.2.2 (vii), pp. 20–21),
  in the form `exists_adelicHeight_map_le_rational_mul`;
- the boundedness of chamber conjugates of compact unipotent sets,
  `exists_adelicHeight_conj_unipotent_le`.

The route needs no bound of the conjugation count by the modulus `δ_{P₀}(a)` on Siegel sets
and no Haar measure computation in Siegel coordinates. The cosets assigned to an index `κ`
contribute at most `Φ_κ · haar(D C)`. The growth of `σ_{[G]}` in the dyadic coordinates of the
Siegel representatives makes these bounds summable.

## Checks

`lean_check` of the module, with a Lake build, reports no errors or warnings. The declaration
inspection of `Langlands.Global.rationalQuotientSummableLogHeight` reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`.
