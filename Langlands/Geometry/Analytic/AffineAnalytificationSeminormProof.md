# Proof: points of the affine analytification as multiplicative seminorms

Lean module: `Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof`.

Main theorem: `Langlands.Analytic.AffineAnalytification.affineAnalytificationSeminorm`,
of type `AffineAnalytificationSeminormStatement.{u, v}`.

The target statement is
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationSeminormStatement`
(module `Langlands.Geometry.Analytic.AffineAnalytificationSeminormStatement`).
For a complete, ultrametric, nontrivially normed field `K` and a finite polynomial
presentation `P` of a commutative `K`-algebra `A`, it asserts

```
IsEmbedding (fun (x : Space K P) (a : A) => pointSeminorm K P x a) ∧
  range (pointSeminorm K P) = {ν : MulRingSeminorm A | ExtendsNorm K ν}.
```

The proof imports only the statement module. That module imports
`AffineAnalytificationSeminorm`, which in turn imports the published
`AffineAnalytificationGluing` and `Spectrum.Properties`. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

The complete initial proof and its documentation were supplied by Worker 3519
in this task's shared draft. Worker 279 checked the proof over the current Library
and prepared this submission. The published statement and all its imports are
unchanged. Both universe parameters `u, v` are retained.

All auxiliary declarations live in the namespace
`Langlands.Analytic.AffineAnalytification.SeminormComparison`. They are internal
steps of this proof.

## Implemented route

Throughout, `ν : MulRingSeminorm A` satisfies `hν : ExtendsNorm K ν`, that is,
`ν (algebraMap K A c) = ‖c‖` for every `c : K`. The `i`-th generator of `P` is
`P.map (X i)`.

### Step 1: `ν` is ultrametric

- `natCast_le_one`: `ν (n : A) ≤ 1` for every natural number `n`. The proof
  rewrites `n` as the image of `n : K` and uses `hν` and
  `IsUltrametricDist.norm_natCast_le_one`.
- `map_sum_le_sum`: the triangle inequality for finite sums, by induction on the
  finite set.
- `add_le_max`: `ν (a + b) ≤ max (ν a) (ν b)`. Put `M = max (ν a) (ν b)`. The
  binomial theorem (`add_pow`), `map_sum_le_sum` and `natCast_le_one` give
  `ν (a + b) ^ N ≤ (N + 1) * M ^ N` for every `N`. If `ν (a + b) > M`, two cases
  give a contradiction. When `M = 0`, the case `N = 1` already gives one. When
  `M > 0`, the ratio `ν (a + b) / M` is greater than `1`. Then
  `Real.exists_natCast_add_one_lt_pow_of_one_lt` gives an `N` with
  `N + 1 < (ν (a + b) / M) ^ N`, which contradicts the estimate.
- `map_sum_le_of_le`: if every term of a finite sum has `ν` at most `C ≥ 0`, so
  does the sum. The proof is by induction, using `add_le_max`.

### Step 2: the Gauss bound

- `map_monomial_le`: if every generator value has `ν` at most `R`, then a
  monomial `c X^d` evaluated at the generators has `ν` at most
  `‖c‖ * ∏ R ^ dᵢ`. The proof uses multiplicativity, `hν` for the coefficient,
  `Finset.prod_le_prod₀` and `pow_le_pow_left₀`.
- `gauss_bound`: assume every generator value has `ν` at most `radius K m`. Then
  for every polynomial `p`, `ν (P.map p)` is at most the norm of `p` in the Tate
  algebra of polyradius `polyradius K P.arity m`. The proof writes `p` as the sum
  of its monomials (`MvPolynomial.as_sum`) and applies `map_sum_le_of_le`. Each
  monomial is then bounded by `map_monomial_le` and the Library bound
  `GeneralizedTateAlgebra.weighted_norm_coeff_le` with `coeff_polynomialMap`.
  That bound says the weighted coefficient is at most the Tate norm.

### Step 3: extension to the Tate algebra

Fix a level `m` with `hR : ∀ i, ν (P.map (X i)) ≤ radius K m`.

- `tateValue P ν m f` is the infimum over polynomials `p` of
  `ν (P.map p) + ‖f - p‖`, with `p` mapped into the Tate algebra by
  `polynomialMap`. This is the McShane inf-convolution formula. The infimum is
  bounded below by `0` (`tateValue_bddBelow`), and `tateValue_le` records that
  each term bounds it.
- `tateValue_polynomial`: on a polynomial `q` the value is `ν (P.map q)`. The
  term `p = q` gives `≤`. For `≥`, the triangle inequality gives
  `ν (P.map q) ≤ ν (P.map p) + ν (P.map (q - p))`, and `gauss_bound` bounds the
  last term by `‖q - p‖`.
- `tateValue_le_add` and `continuous_tateValue`: `tateValue` is 1-Lipschitz
  (`LipschitzWith.of_le_add`), hence continuous.
- `tatePoint hν hR`: a point of `BanachSpectrum` of the Tate algebra with
  underlying function `tateValue P ν m`. Zero and one are polynomials, so
  `tateValue_polynomial` handles them. Multiplicativity, subadditivity, symmetry
  under negation and the bound `≤ ‖f‖` each hold on polynomials, by
  `tateValue_polynomial` and step 2. Each condition defines a closed set, because
  `tateValue` is continuous. They therefore hold everywhere, by
  `isClosed_property` or `isClosed_property2` and the density of polynomials
  (`GeneralizedTateAlgebra.denseRange_polynomialMap`).

### Step 4: descent to the chart

- `ideal_le_kernel`: the closed relation ideal `(algebra K P m).ideal` lies in
  the kernel of `tatePoint hν hR`. Every relation `p` (a polynomial with
  `P.map p = 0`) has value `ν 0 = 0` by `tateValue_polynomial`. So the span of
  the relations lies in the kernel. The kernel is closed, since `tateValue` is
  continuous. The relation ideal is the closure of the span (`Ideal.coe_closure`),
  so it also lies in the kernel (`closure_minimal`).
- `chartPoint hν hR`: the induced point of `BanachSpectrum (algebra K P m)`,
  obtained by `BanachSpectrum.descend`.
- `chartSeminorm_chartPoint`: `chartSeminorm K P m (chartPoint hν hR) = ν`. Every
  `a : A` is `P.map p` for some polynomial `p` (`P.surjective`). Its image in the
  chart algebra is the image of `p` (`PolynomialLocus.algebraMap_map`), and the
  descended point takes the value `tateValue` there. This is `ν (P.map p)` by
  `tateValue_polynomial`.
- `exists_level`: some level `m` bounds all generator values. Take `m` with
  `radius K m` greater than the finite sum of the generator values
  (`exists_radius_gt`).

### Step 5: the image

`range_pointSeminorm`. Every point seminorm extends the norm
(`pointSeminorm_extendsNorm`, from `AffineAnalytificationSeminorm`). Conversely,
given `ν` with `hν`, take `m` from `exists_level`. Then the point
`chart K P m (chartPoint hν hm)` has seminorm `ν`, by `pointSeminorm_chart` and
`chartSeminorm_chartPoint`.

### Step 6: injectivity

- `continuous_spectrum_apply`: a spectrum point of a normed ring is 1-Lipschitz,
  by subadditivity and `le_norm`. So it is continuous.
- `denseRange_chartAlgebraMap`: the image of `A` is dense in the `m`-th chart
  algebra. Polynomials are dense in the Tate algebra. The presentation map onto
  the chart algebra is continuous and surjective (`presentationMap_surjective`),
  so it carries a dense set to a dense set, and each image of a polynomial is the
  image of an element of `A`.
- `chartSeminorm_injective`: two chart points with the same seminorm on `A` agree
  on a dense set. They are continuous, so they are equal (`Continuous.ext_on`).
- `pointSeminorm_injective`: two points of `Space K P` come from charts `m` and
  `k` (`exists_chart`). Both are pulled to the common chart `max m k`
  (`chart_pull`), and `pointSeminorm_chart` with `chartSeminorm_injective`
  finishes.

### Step 7: the embedding

`isEmbedding_pointSeminorm`. Write `Φ x = (a ↦ pointSeminorm K P x a)`. `Φ` is
continuous, since each coordinate is continuous by
`continuous_pointSeminorm_apply`. By step 6, `Φ` is injective. It remains to show
`Φ` is inducing, which is done with `isInducing_iff_nhds`. One inequality of
neighbourhood filters is continuity. For the other, let `U` be a neighbourhood of
a point `x = chart K P m s`.

- `x` lies in the open polydisc `openDisc K P m` (`range_chart_subset_openDisc`),
  and that disc lies in the image of the chart `m + 1`
  (`openDisc_subset_range_chart`). So `x = chart K P (m + 1) t` for some `t`.
- The chart space is compact and `A → ℝ` is Hausdorff. So `Φ ∘ chart K P (m + 1)`
  is a continuous injection from a compact space, hence a closed embedding
  (`Continuous.isClosedEmbedding`). Its neighbourhood filter at `t` is therefore
  the pullback of the one at `Φ x`. This gives a neighbourhood `V` of `Φ x` whose
  preimage under `Φ ∘ chart K P (m + 1)` lies in the preimage of `U`.
- `coordinateNorm_eq`: the `i`-th chart coordinate of a point is its seminorm at
  the `i`-th generator (`coordinateNorm_chart`, `PolynomialLocus.polynomialMap_X`).
  So the open set
  `W = {f : A → ℝ | ∀ i, f (P.map (X i)) < radius K (m + 1)}` contains `Φ x`, and
  its preimage under `Φ` lies in the open polydisc of level `m`.
- Every `z` with `Φ z ∈ V ∩ W` lies in `openDisc K P m`, hence in the image of
  the chart `m + 1`, hence in `U`. So `U` contains the preimage of the
  neighbourhood `V ∩ W` of `Φ x`.

The main theorem `affineAnalytificationSeminorm` combines steps 7 and 5.

## Mathematical content

This proves, for the Library's polynomial-locus model, the description in
Berkovich 1990, Remark 3.4.2 (printed p.64/PDF p.78), of `Spec(A)^an` as the
multiplicative seminorms on `A` extending the norm of `K`. It uses the topology
of Definition 1.5.1 (printed p.19/PDF p.33). The source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Berkovich gives no separate proof of the remark. The Lean route above is
self-contained over the Library's chart construction. The ultrametric bound (step 1) is the usual power trick. The
extension from polynomials to the Tate algebra (step 3) uses the
inf-convolution formula and density, rather than a completion argument.

## Scope

The theorem has exactly the hypotheses and conclusion of the published statement,
for arbitrary universes `u, v`. It compares the underlying points and topology
of the affine polynomial-locus model with multiplicative seminorms extending
the norm. The structure sheaf, residue fields, general schemes and the
extension-field description in the second half of Remark 3.4.2 are outside
this theorem.
