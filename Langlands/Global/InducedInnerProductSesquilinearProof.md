# Sesquilinearity of the induced inner product `(·,·)_P`

Module `Langlands.Global.InducedInnerProductSesquilinearProof` proves

```
theorem Langlands.Global.inducedInnerProductSesquilinear :
    InducedInnerProductSesquilinearStatement
```

`InducedInnerProductSesquilinearStatement` is in `Langlands.Global.AdelicLocalWavePacketStatement`.
It is premise (D) of the reduction of Lapid 2011, Lemma 10 (`BoundedWavePacketStatement`). It says
that the inner product `(·,·)_P` (`inducedInnerProduct`, Lapid §2, p.311) is sesquilinear on finite
linear combinations of elements `v j` of `A^2_P`:

`(∑ j, z j v j, ∑ j, z' j v j)_P = ∑ j, ∑ j', z j · conj (z' j') · (v j, v j')_P`.

The hypotheses include a Levi projection `π : P ⟶ M` with `l ≫ π = 𝟙 M`. The proof uses `π`,
the presentation `r` (only for `IsConnectedReductive M`), compactness of `K`, the Haar property of
`μ_M`, continuity and compact support of `β`, and `v j ∈ A^2_P`. It does not use the other
hypotheses, such as `IsIwasawaCompatibleMeasure`, `∫ β = 1`, `IsMaximalCompactSubgroup F G K` or
`IsClosedSubgroup rho`.

## The proof implemented in Lean

Write `(φ, ψ)_P = ∫_K ∫_{M(F) \ M(𝔸)} kernel φ ψ k m`, where
`kernel φ ψ k m = β(y(m)) δ_P(m)⁻¹ φ(m k) conj ψ(m k)` is evaluated at the chosen representative
`m = x.out` of each coset (`inducedInnerProduct_eq_kernel`, by `rfl`). Here `y(m)` are the
coordinates of `H_P(m)`, `δ_P(m)⁻¹ = m^{-2ρ_P}`, and `m k` means `p(l(m)) k`.

1. **Algebra and Fubini.** The integrand of the left side equals
   `∑ j, ∑ j', z j conj(z' j') kernel (v j) (v j')` (`kernel_sum`). If each
   `kernel (v j) (v j')` is integrable for the product measure `dk × dm` on
   `K × M(F) \ M(𝔸)`, the iterated integrals split termwise (`integral_integral_sum_sum`: integrability
   of the sections for almost every `k`, then `integral_finsetSum` twice). So everything reduces
   to the integrability of `kernel φ ψ` for `φ, ψ ∈ A^2_P` (`integrable_kernel`).

2. **Invariance and measurability.** Every `φ ∈ A^2_P` is continuous and left invariant under
   `M(F)`, embedded by `l ≫ p`. `H_P` vanishes on `M(𝔸)¹`, which contains `M(F)`. So `kernel φ ψ k`
   is left `M(F)`-invariant in `m` (`kernel_rational_mul`). By the `A^n_P` equivariance and
   `|δ_P(a)⁻¹| |a^{ρ_P}|² = 1` (`norm_modulus_mul_sq`),
   `normWeight φ k m = |δ_P(m)⁻¹| |φ(m k)|²` is left invariant under `A_M M(F)`
   (`canonicalRationalSubgroup_le_leftStabilizer`). A continuous left-invariant function evaluated at
   chosen representatives is continuous on `X × Γ \ H`: `Prod.map id mk` is an open quotient map
   (`continuous_prod_out`, `continuous_out`). This gives the measurability needed for Tonelli and
   for `Integrable`.

3. **Pointwise bound.** `|kernel φ ψ| ≤ |kernel φ φ| + |kernel ψ ψ|` (`norm_kernel_le`) and
   `|kernel φ φ k m| = |β(y(m))| · normWeight φ k m` (`norm_kernel_self`). So it suffices that
   `kernel φ φ` is integrable (`integrable_kernel_self`).

4. **Fundamental domain and factorization.** Let `T₀ → M` be the canonical split component of `M`.
   The Library supplies an injective restriction of characters with finite-index image, given
   `centralSplitTorusCharacter` and `M` connected reductive, which comes from `r.isCompatible.levi`.
   Fix a splitting `T₀ ≅ 𝔾_m^I` and let `A` be the positive torus.
   `normOneDecomposition : A × M(𝔸)¹ ≃ₜ M(𝔸)`, `(a, n) ↦ a n`, carries
   `normalizedPositiveHaarMeasure × haar` to `haar` (`measurePreserving_normOneDecomposition`).
   With `D¹` the Library's Borel fundamental domain of `M(F)` in `M(𝔸)¹`,
   `productDomain = {m | normOneFactor m ∈ D¹}` is a fundamental domain of `M(F)` in `M(𝔸)`
   (`isFundamentalDomain_productDomain`, using centrality of `A`).
   For a left `M(F)`-invariant `f ≥ 0` with `f(a n) = b(a) w(n)`:
   `∫_{M(F) \ M(𝔸)} f = (∫_A b) · ∫_{D¹} w` for the quotient of `haar`
   (`lintegral_rationalQuotient_haar`: `discreteQuotientMeasure_eq`, `lintegral_map`, the
   measure-preserving decomposition, `Measure.prod_restrict` and `lintegral_prod_mul`). For an
   `A_M M(F)`-invariant `W ≥ 0`, `∫_{[M]} W dcanonicalMeasure = ∫_{D¹} W`, because
   `canonicalMeasure` is the image of the quotient of `haar` on `M(𝔸)¹` (`lintegral_canonical`).
   For `f = |kernel φ φ k ·|`, the identity
   `|kernel φ φ k (a n)| = |β(y(a))| · normWeight φ k n` (`characterLog_map_mul_normOne`,
   `normWeight_splitComponent_mul`) gives
   `∫_{M(F) \ M(𝔸)} |kernel φ φ k| = C · ∫_{[M]} normWeight φ k` with `C = ∫_A |β(y(a))| da`
   (`exists_lintegral_rationalQuotient_kernel`).

5. **The constant `C` is finite.** In logarithmic coordinates `A ≃ₜ ℝ^I`
   (`positiveCoordinates`), the map `a ↦ y(a)` is the linear map `torusCoordinateMap`. It is the
   composite of
   - the dual of the finite-index restriction `X^*(M) → X^*(T₀)`, a linear isomorphism
     (`realCharacterDualRestrictionEquiv`);
   - the dual `Hom(X^*(M), ℝ) → Hom(X^*(P), ℝ)` of restriction along `l`, injective because `π`
     gives a left inverse (`realCharacterDualMap_injective`); this is where `l ≫ π = 𝟙 M` is used;
   - the coordinates dual to the basis `e`, injective (`coordinateMap_injective`).

   So `torusCoordinateMap` is injective, hence a closed embedding. Therefore `a ↦ β(y(a))` is
   continuous with compact support (`hasCompactSupport_positive`), and its integral against the
   Haar measure on `A` is finite (`lintegral_positive_lt_top`).

6. **Conclusion.** By Haar uniqueness, `μ_M = c · haar` (`isMulLeftInvariant_eq_smul`), so the
   quotient measure scales by `c`. Tonelli on `K × M(F) \ M(𝔸)` and on `K × [M]` gives
   `∫ |kernel φ φ| = c · C · ∫_{K × [M]} δ_P⁻¹ |φ|² < ∞`. The last integral is finite by the `A^2_P`
   condition in `IsSquareIntegrableInducedForm`.

## Provenance

Lapid 2011 (§2, p.311) treats this absolute convergence as standard. The route above is the usual
one: unfold `M(F) \ M(𝔸) = A_M × M(F) \ M(𝔸)¹` and integrate out `A_M` against the weight `β`. The
internal definitions `weight`, `kernel`, `normWeight`, `coordinateMap`, `torusCoordinateMap`,
`positiveCoordinates`, `normOneDomain`, `productDomain` and `Langlands.Automorphic.UnitaryCharacterPairing.leftStabilizer` are proof devices
local to this module. They are not new mathematical notions.
