# Uniform moderate growth of Eisenstein series from their meromorphic continuation

Module `Langlands.Global.AdelicEisensteinUnitaryGrowthReduction`, namespace
`Langlands.Global`. It states `EisensteinUnitaryUniformGrowthReductionStatement` and proves it
(`eisensteinUnitaryUniformGrowthReduction`):

```
EisensteinMeromorphicContinuationStatement.{0} → EisensteinUnitaryUniformGrowthStatement
```

- The premise `EisensteinMeromorphicContinuationStatement` (module
  `Langlands.Global.AdelicEisensteinContinuationStatement`) is Bernstein–Lapid 2024,
  Theorem 2.3 (1), in the Fréchet form of their Corollary at the end of §8.6: near every
  parameter, in every linear chart, the Eisenstein series is a meromorphic function with values
  in one space `𝔉^R_L = UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`, with `L`
  open, for a closed matrix embedding `rho` of positive size `N`.
- The conclusion `EisensteinUnitaryUniformGrowthStatement` (module
  `Langlands.Global.AdelicEisensteinUnitaryGrowthStatement`): for `φ ∈ A^2_P`, a pointwise
  continuation `(E, D)` of `E(φ, ·)` with `i𝔞_P^* ⊆ D`, real coordinates
  `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a compact `C ⊆ ℝⁿ`, there are an open `L ≤ G(𝔸_f)`, an exponent
  `R` and a family `f` with underlying functions `E(i e(x))` for `x ∈ C` and
  `IsUniformGrowthFamily rho hsmooth hcalc L R f C`.

The module does not prove the premise. Holomorphy of `E` on `i𝔞_P^*` (Lapid 2011,
Proposition 6) is not used as a premise: the conclusion assumes that each `λ ↦ E λ g` is
holomorphic on `D ⊇ i𝔞_P^*`, and the proof shows that this scalar holomorphy and the Fréchet
continuation give the uniform bounds.

## Sources and provenance

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`: Theorem 2.3 (p.191), §3.1 (weakly
holomorphic and meromorphic vector-valued functions, p.192), and the Corollary at the end of
§8.6 (p.226).

Provenance: derived. This is the passage from the Corollary of §8.6 to bounds uniform on a
compact set of unitary parameters that the Markdown of
`AdelicEisensteinUnitaryGrowthStatement` describes: holomorphy of the Fréchet-valued
continuation at the points of `i𝔞_P^*`, its local boundedness, a finite cover of the compact
set with a common level and exponent, and the case `N = 0`. Since the premise is formulated
with the Library's spaces `𝔉^R_L`, whose weight is a power of the adelic norm of `rho`, no
comparison of height functions is needed here.

## Declarations

| Declaration | Kind |
| --- | --- |
| `UniformGrowthFrechetSpace.norm_evaluate_le` | theorem |
| `Langlands.Global.ArthurTruncation.exists_pos_le_adelicSourceNorm` | theorem |
| `rpow_le_rpow_sub_mul_rpow` | theorem |
| `exists_imaginary_coordinates` | theorem |
| `exists_local_frechet_open_of_eisensteinContinuation` | theorem |
| `exists_local_uniformGrowth_bound` | theorem |
| `exists_uniformGrowthFamily_of_pos` | theorem |
| `exists_uniformGrowthFamily_of_rank_zero` | theorem |
| `EisensteinUnitaryUniformGrowthReductionStatement` | statement |
| `eisensteinUnitaryUniformGrowthReduction` | theorem (proof of the statement) |

A *pointwise continuation* `(E, D)` of the Eisenstein series of `φ` is as in
`AdelicEisensteinContinuationLocalFrechet.md`: every `λ ↦ E λ g` is meromorphic in linear
coordinates with domain of holomorphy `D`, and `E λ = E(φ, λ)` for `R`-regular `λ`.

## Proofs as implemented

### Growth lemmas

- `UniformGrowthFrechetSpace.norm_evaluate_le`: for `w ∈ 𝔉^R_L`, `u` in the enveloping algebra
  and `g ∈ G(𝔸)`, `|(u w)(g)| ≤ ‖D_u w‖ ‖g‖^R`, where `D_u w = (u w) ‖·‖^{-R}` is the weighted
  derivative (`weightedDerivativeCLM`) with its supremum norm. This is the definition of
  `D_u` and the bound of a bounded function by its norm.
- `Langlands.Global.ArthurTruncation.exists_pos_le_adelicSourceNorm`: for `N > 0` the adelic norm of `rho` is bounded below by
  `c₀ = N^{-∑ mult}`, since the height `N^{∑ mult} ‖g‖` is at least `1`
  (`RepresentationGrowth.one_le_adelicHeight`).
- `rpow_le_rpow_sub_mul_rpow`: for `0 < c₀ ≤ x` and `R' ≤ R`,
  `x^{R'} ≤ c₀^{R' - R} x^R`.
- `exists_imaginary_coordinates`: for real coordinates `e` there are complex coordinates `e₀`
  of `X^*(P) ⊗ ℂ` (from `Module.finBasis`) and a continuous `A : ℝⁿ → ℂ^m` with
  `e₀ (A x) = i e(x)`; `A` is real linear between finite-dimensional spaces.

### Local Fréchet data

`exists_local_frechet_open_of_eisensteinContinuation` is the statement of
`exists_local_frechet_of_eisensteinContinuation` (module
`Langlands.Global.AdelicEisensteinContinuationLocalFrechet`) with the openness of the level
`L` kept in the conclusion. Its proof is the same: the continuation `E'` of the premise is
meromorphic at every point of `G(𝔸)` with one domain (`exists_isMeromorphicOn_of_local`), and
agrees with `E` on the common domain of holomorphy by uniqueness from the regular parameters
(`ParabolicRootPresentation.eqOn_of_regularParameter`); the domain of the Fréchet-valued
function is shrunk to that common domain.

### Local uniform bounds

`exists_local_uniformGrowth_bound`: assume the premise, `N > 0`, and a pointwise continuation
`(E, D)` of `E(φ, ·)` for `φ` automorphic on `U(𝔸) M(F) \ G(𝔸)`. For a chart `e₀` and
`s₀` with `e₀ s₀ ∈ D` there are `ε > 0`, `R`, an open `L` and `v : ℂ^m → 𝔉^R_L` such that the
underlying function of `v s` is `E (e₀ s)` for `s` in the ball `B(s₀, ε)`, and every weighted
derivative `D_u (v s)` is bounded on that ball.

1. The local Fréchet data give a meromorphic `f` near `s₀`. `IsMeromorphicOn.exists_flat_numerator`
   (module `Langlands.Global.EisensteinContinuationNormalization`) gives an open `W₁ ∋ s₀`, a
   holomorphic denominator `den` and a weakly holomorphic numerator `H` on `W₁`, and an open
   `U₁` with `W₁ ⊆ closure U₁`, `den ≠ 0` on `U₁` and `H(s) = den(s) E(e₀ s)` on `U₁`.
2. On `U₀ = W₁ ∩ e₀⁻¹ D` both sides of `H(s)(g) = den(s) E(e₀ s)(g)` are continuous in `s` for
   each `g` (the right side because `s ↦ E (e₀ s) g` is holomorphic on `e₀⁻¹ D`), so the
   identity extends from `U₀ ∩ U₁` to `U₀`. The germ of `den` at `s₀` is not zero, since every
   neighbourhood of `s₀` meets `U₁`.
3. `UniformGrowthFrechetSpace.exists_weaklyHolomorphic_of_mul_eq_eval` (module
   `Langlands.Automorphic.GroupSchemeUniformGrowthRemovableSingularity`) gives an open
   `V ∋ s₀` and `v`, weakly holomorphic on `V`, with underlying functions `E (e₀ s)`.
4. A weakly holomorphic family is continuous in the topology of `𝔉^R_L`
   (`UniformGrowthFrechetSpace.continuousOn_of_differentiableOn_dual`). Each `D_u ∘ v` is
   therefore continuous on a closed ball in `V`, hence bounded on it.

### The compact set, `N > 0`

`exists_uniformGrowthFamily_of_pos`. Let `A` and `e₀` be as in `exists_imaginary_coordinates`.
Every `e₀ (A x) = i e(x)` lies in `D`. The local bounds at the points `A x` give balls
`B(A x, ε_x)`, exponents `R_x`, open levels `L_x`, vectors `v_x` and bounds `B_x(u)`. The open
sets `A⁻¹ B(A x, ε_x)`, `x ∈ C`, cover the compact `C`; let `t` be a finite subcover. Put
`R = ∑_{i ∈ t} |R_i|`, `L = ⨅_{i ∈ t} L_i` (open as a finite intersection of open sets), and
for `x ∈ C` choose `i(x) ∈ t` with `A x ∈ B(A i(x), ε_{i(x)})` and let `f x` be the function of
`v_{i(x)} (A x)` (for `x ∉ C`, `f x = 0`). Then:

- the underlying function of `f x` is `E (e₀ (A x)) = E (i e(x))`;
- `f x` is right invariant under `L_{i(x)}`, hence under `L ≤ L_{i(x)}`;
- for each `u`, with `c₀` from `Langlands.Global.ArthurTruncation.exists_pos_le_adelicSourceNorm`,
  `|(u f x)(g)| ≤ max(B_i(u), 0) ‖g‖^{R_i} ≤ max(B_i(u), 0) c₀^{R_i - R} ‖g‖^R` with
  `i = i(x)` and `R_i ≤ R`, and the sum over `i ∈ t` of `max(B_i(u), 0) c₀^{R_i - R}` is one
  constant `M` for all `x ∈ C` and `g`.

### The case `N = 0`

`exists_uniformGrowthFamily_of_rank_zero`. A closed embedding into `GL_0` makes `G(𝔸)` a
single point (`subsingleton_adelicGroupPoints_of_rank_zero`). The function
`x ↦ c(x) = E (i e(x)) 1` is continuous, as the composite of `s ↦ E (e₀ s) 1`, holomorphic on
`e₀⁻¹ D`, with `A`; it is bounded on `C` by some `B_c`. Let `1` be the constant function, an
element of `FinitePlotSmoothRationalFunctions` (`ofRationalSmoothFunction`; constant slices are
plot-smooth by `isPlotSmooth_const`, and `⊤` is an open level). The family is `f x = c(x) • 1`,
with level `L = ⊤`, invariant because `G(𝔸)` is a point, and exponent `R = 0`. Then
`(u f x)(g) = c(x) (u 1)(1)`, so `|(u f x)(g)| ≤ B_c |(u 1)(1)| = B_c |(u 1)(1)| ‖g‖^0`.

### The reduction

`eisensteinUnitaryUniformGrowthReduction` introduces the data of the conclusion and splits on
`N`: for `N = 0` it applies `exists_uniformGrowthFamily_of_rank_zero`, and for `N > 0` it
applies `exists_uniformGrowthFamily_of_pos` to `φ`, which is automorphic on
`U(𝔸) M(F) \ G(𝔸)` by the first clause of `IsSquareIntegrableInducedForm`. Square
integrability is not used beyond that clause.
