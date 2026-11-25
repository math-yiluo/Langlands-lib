# Positive definiteness of `(·,·)_P` on `A^2_P` in Gram form

Module `Langlands.Global.AdelicInducedInnerProductGramCoordinateProof` proves

```
theorem Langlands.Global.inducedInnerProductGram_of_torusCoordinates : InducedInnerProductGramStatement
```

`InducedInnerProductGramStatement` is in `Langlands.Global.AdelicInducedInnerProductGramStatement`.
It is the positive definiteness of the inner product `(φ, ψ)_P = ∫_{A_M U(𝔸) M(F) \ G(𝔸)} φ ψ̄`
attached to the norm `‖φ‖_P` of Lapid 2011, §2 (printed p.311, PDF p.320 of the registered
source `lapid-2011-asymptotic-inner-product-truncated-eisenstein`). In Iwasawa coordinates this
inner product is a positive Haar-measure scalar times `inducedInnerProduct K hK.isCompact p l μM e β`. For `φ i ∈ A^2_P` and
`x i ∈ ℂ`, the statement says that the Gram sum `∑ i, ∑ i', x i · conj (x i') · (φ i, φ i')_P`
is a nonnegative real number (`0 ≤` in `ComplexOrder`), and that it is `0` exactly when
`∑ i, x i • φ i = 0`. Lapid defines the norm and gives no separate argument for positive
definiteness. The proof below computes directly in the
Library's model of the quotient.

The statement and its hypotheses are unchanged. The proof uses: the rational Levi `l` (through
`IsRationalLeviSubgroup`, which supplies a retraction `π : P ⟶ M` with `l ≫ π = 𝟙 M`, a unipotent
radical, and `IsConnectedReductive M`); the supplied radical `iU` together with
`IsIso (subgroupMultiplication l iU)` (to decompose points of `P(𝔸)`); `hK` (compactness of `K`
and `P(𝔸) K = G(𝔸)`); the Haar property of `μ_M`; continuity, compact support and `∫ β = 1` of
`β`; and `φ i ∈ A^2_P`. It does not use `IsConnectedReductive G`, `IsParabolicSubgroup p` or
`LeviSubgroup.IsGeometricUnipotentRadical iU`. The weight `β` is not assumed nonnegative.

## Notation

`kernel φ ψ g m = β(y(m)) δ_P(m)⁻¹ φ(m g) conj ψ(m g)` and
`normWeight φ g m = |δ_P(m)⁻¹| |φ(m g)|²` are the integrands of
`Langlands.Global.InducedInnerProductSesquilinearProof`. Here `m g` means `p(l(m)) g`,
`y(m) = parameterCoordinates F P e (characterLog F P (l m))` and `δ_P(m)⁻¹ = m^{-2ρ_P}`.
`T₀ → M` is the canonical split component of `M`, `A` its positive points, and
`normOneDecomposition : A × M(𝔸)¹ ≃ₜ M(𝔸)`, `(a, n) ↦ a n`. `D¹` (`normOneDomain`) is the
Library's Borel fundamental domain of `M(F)` in `M(𝔸)¹`, and `A × D¹` (`productDomain`) is a
fundamental domain of `M(F)` in `M(𝔸)` (`isFundamentalDomain_productDomain`). `ν_A` is
`normalizedPositiveHaarMeasure`, for which `normOneDecomposition` carries `ν_A × haar` to `haar`.

## The proof implemented in Lean

### 1. The Gram sum is `(Φ, Φ)_P`

Let `Φ = ∑ j, x j • φ j`, written `fun g => ∑ j, x j * φ j g`. By `kernel_sum`,
`kernel Φ Φ = ∑ j, ∑ j', x j conj(x j') kernel (φ j) (φ j')`. Each `kernel (φ j) (φ j')` is
integrable on `K × M(F) \ M(𝔸)` (Library `integrable_kernel`, which uses `l ≫ π = 𝟙 M`). Then
`integral_integral_sum_sum` gives

`Gram sum = ∫_K ∫_{M(F) \ M(𝔸)} kernel Φ Φ k m`   (`hgram`),

and `kernel Φ Φ` is integrable on the product (`hkerint`). `Φ` inherits continuity, left
invariance under `U(𝔸) M(F)` and `A_M`-equivariance from the `φ j`. These are pointwise
identities, so they pass to finite sums; full membership of `Φ` in `A^2_P` is never needed.

### 2. The coordinates `y` identify `A` with `ℝⁿ` (`torusCoordinateHomeomorph`)

In logarithmic coordinates `positiveCoordinates : A ≃ₜ ℝ^I`, the map `a ↦ y(a)` is the linear map
`torusCoordinateMap` (`parameterCoordinates_positivePointMap`). This map is the composite of four
linear maps, each a bijection:

- the inverse of the coordinate isomorphism `Hom(X^*(T₀), ℝ) ≃ ℝ^I`;
- the dual of restriction of characters `X^*(M) → X^*(T₀)`, an isomorphism
  (`realCharacterDualRestrictionEquiv`; the restriction is injective with finite-index image);
- `realCharacterDualMap l : Hom(X^*(M), ℝ) → Hom(X^*(P), ℝ)`, `H ↦ H ∘ (restriction along l)`.
  It is injective because `π` gives a left inverse (Library `realCharacterDualMap_injective`).
  It is surjective (`realCharacterDualMap_surjective_of_levi`), with preimage of `H` equal to
  `H ∘ (restriction along π)`. This uses that restriction of characters along `l` is injective
  (`characterRestrict_injective_of_levi`): write a point of `P` as `l(m) u` with `u` in the
  unipotent radical; a rational character is trivial on a unipotent group
  (`IsUnipotent.comp_eq_one_of_isSplitTorus`), so it is determined by its restriction to `M`.
  This lemma reproduces a private lemma of `Langlands.Global.AdelicIntertwiningImaginaryUnitarityReduction`,
  under a new public name in this module's namespace;
- the coordinates `H ↦ (⟨e(b_j), H⟩)_j` dual to `e`. These are injective (Library
  `coordinateMap_injective`) and surjective (`coordinateMap_surjective`). For `y ∈ ℝⁿ` let
  `ψ = (v ↦ ∑ j y_j v_j) ∘ e⁻¹` and `H(χ) = ψ(1 ⊗ χ)`. Then `⟨μ, H⟩ = ψ(μ)` for all
  `μ ∈ X^*(P) ⊗ ℝ`, by induction on tensors, so the coordinates of `H` are `y`.

So `torusCoordinateMap` is a linear equivalence (`torusCoordinateMap_bijective`), and
`torusCoordinateHomeomorph : A ≃ₜ ℝⁿ` is the composite `y` with
`y(a b) = y(a) + y(b)` (`torusCoordinateHomeomorph_mul`, from `characterLog_mul`).

### 3. `B = ∫_A β(y(a)) dν_A` is positive (`integral_positive_weight_pos`)

`isAddHaarMeasure_map_of_map_mul`: the image of a Haar measure under a homeomorphism `f` with
`f(x y) = f(x) + f(y)` is an additive Haar measure. This holds because local finiteness and
positivity on open sets transfer along homeomorphisms, and `(g + ·) ∘ f = f ∘ (f⁻¹(g) · ·)`.
By uniqueness of additive Haar measure on `ℝⁿ`, the image of `ν_A` under `y` is `c' · volume`
with `c' = addHaarScalarFactor > 0`. Hence
`∫_A β(y(a)) dν_A = c' ∫ β = c' > 0` (`integral_comp_pos`). No sign condition on `β` is used.

### 4. The inner integral (`kernel_self_data`, first part)

For each `g`:

- `kernel Φ Φ g m = β(y(m)) · normWeight Φ g m` (`kernel_self_eq`). This holds because
  `δ_P(m)⁻¹` is a positive real number (`ofReal_norm_parameterPower_neg_modulusParameter`) and
  `z conj z = |z|²`;
- for `a ∈ A` and `n ∈ M(𝔸)¹`: `y(a n) = y(a)` (`characterLog_map_mul_normOne`), and
  `normWeight Φ g (a n) = normWeight Φ g n` (`normWeight_splitComponent_mul`, from the
  `A_M`-equivariance). So `kernel Φ Φ g (a n) = β(y(a)) · normWeight Φ g n`.

`integral_rationalQuotient_haar` is the Bochner analogue of the Library's
`lintegral_rationalQuotient_haar`. For a continuous left `M(F)`-invariant `f` with
`f(a n) = b(a) w(n)`, the integral of `f` over `M(F) \ M(𝔸)` for the quotient of `haar` is
`(∫_A b dν_A) · ∫_{D¹} w`. The proof uses `discreteQuotientMeasure_eq` with `A × D¹`,
`integral_map`, `MeasurePreserving.setIntegral_preimage_emb` for `normOneDecomposition`,
`Measure.prod_restrict` and `integral_prod_mul`. The last of these holds without integrability
hypotheses: if either factor is not integrable, both sides are `0`. This is why the signed `β`
causes no difficulty. With `μ_M = c · haar` (`c = haarScalarFactor > 0`, so the quotient
measures differ by `c`), we get

`∫_{M(F) \ M(𝔸)} kernel Φ Φ g m dm = C · W(g)`, with `C = c · B > 0` and
`W(g) = ∫_{D¹} normWeight Φ g n dn ≥ 0`.

### 5. Nonnegativity

By steps 1 and 4, the Gram sum equals `C · ∫_K W(k) dk`, a real number (`integral_complex_ofReal`,
`integral_const_mul`). It is `≥ 0` because `C > 0` and `W ≥ 0`.

### 6. Vanishing

Suppose the Gram sum is `0`. Then `∫_K W = 0`. Integrability of `kernel Φ Φ` on the product gives
integrability of `k ↦ ∫ kernel Φ Φ k = C · W(k)` (`Integrable.integral_prod_left`). Hence `W` is
integrable and `W = 0` almost everywhere on `K` (`integral_eq_zero_iff_of_nonneg`). For almost
every `k` the section `kernel Φ Φ k` is also integrable (`Integrable.prod_right_ae`). For such
`k` (`kernel_self_data`, second part):

- `integrableOn_normOneDomain`: if `f(a n) = b(a) w(n)` is integrable on `M(F) \ M(𝔸)` and
  `∫ b ≠ 0`, then `w` is integrable on `D¹`. Transport `f` to `ν_A × haar|_{D¹}`
  (`integrable_map_measure`, `MeasurePreserving.integrableOn_comp_preimage`) and apply
  `integrable_prod_iff'`. It gives integrability of `n ↦ (∫ |b|) · |w(n)|`, and
  `∫ |b| ≥ |∫ b| = B > 0`;
- `eq_zero_of_setIntegral_normOneDomain`: a continuous, nonnegative, left `M(F)`-invariant
  function on `M(𝔸)¹` that is integrable on `D¹` with integral `0` vanishes identically. The
  normalized quotient measure on `M(F) \ M(𝔸)¹` is the image of `haar|_{D¹}`, so the function
  descends to the quotient with integral `0`. The descended function is continuous
  (`continuous_out`) and the quotient measure charges every nonempty open set
  (`LeftCosetSpace.isOpenPosMeasure_discreteQuotientMeasure`), so it is `0`
  (`Continuous.ae_eq_iff_eq`);
- applied to `normWeight Φ k`, this gives `normWeight Φ k n = 0` for all `n ∈ M(𝔸)¹`. Writing
  `m = a n` through `normOneDecomposition` and using `A`-invariance extends this to all
  `m ∈ M(𝔸)`.

For each fixed `m`, `k ↦ normWeight Φ k m` is continuous on `K` and `0` almost everywhere for
the Haar probability measure, which has full support. So it is `0` for every `k`. Since
`δ_P(m)⁻¹ ≠ 0`, we get `Φ(p(l(m)) k) = 0` for all `m ∈ M(𝔸)` and `k ∈ K`
(`form_eq_zero_of_normWeight_eq_zero`).

Finally let `g ∈ G(𝔸)`. By `hK.exists_eq`, `g = p(q) k` with `q ∈ P(𝔸)` and `k ∈ K`.
Decompose `q⁻¹ = l(m) iU(u)` with the inverse of the multiplication isomorphism
(`leviComponent_mul_radicalComponent l iU`). Then `q = iU(u⁻¹) l(m⁻¹)`. The point
`p(iU(u⁻¹))` lies in `U(𝔸) ⊆ U(𝔸) M(F)`, so left invariance gives
`Φ(g) = Φ(p(l(m⁻¹)) k) = 0`. Hence `Φ = 0`.

Conversely, if `∑ i, x i • φ i = 0` then `Φ = 0`. Then `W = 0`, and the Gram sum `C · ∫ W` is `0`.

## Relation to the literature

Lapid 2011, §2, p.311 defines `A^n_P`, the forms `φ` on `U(𝔸) P(F) \ G(𝔸)` with
`φ(a g) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M`. He also defines `A^2_P ⊆ A^n_P` by
`‖φ‖_P² = ∫_{A_M P(F) U(𝔸) \ G(𝔸)} |φ(g)|² dg < ∞`, with Haar measures compatible with the
Iwasawa decomposition and `M(𝔸) = M(𝔸)¹ × A_M`. In `inducedInnerProduct`, the weight `β` on
`ℝⁿ` replaces the integration over `A_M`. The quantity `C ∫_K ∫_{D¹} δ_P(n)⁻¹ |Φ(n k)|²` of
step 4 corresponds informally to Lapid's `‖Φ‖_P²`, up to the positive constant `C`. This
correspondence is not formalized and the proof does not need it. Steps 5 and 6 prove
positivity and definiteness directly for the Lean expression.
