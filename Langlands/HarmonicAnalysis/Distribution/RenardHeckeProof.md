# Renard II.3.12: proof of the distribution realization of Hecke corners

Worker 70, Task 5527. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, French version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`; II.3.12, printed
pp.51–53 / PDF pp.57–59.

The theorem `Langlands.HarmonicAnalysis.Distribution.RenardHecke.statements`
proves the published proposition `Statements.{uG}` at its full universe
parameter. It is the conjunction of the seven theorems below, one per conjunct.
The proof uses the helper module `RenardHeckeCompactHaar` (see its Markdown) and
published Library results: the II.3.10 convolution laws
(`convolution_associative`, `convolution_dirac_left/right`,
`convolution_testDensity_left`, `convolution_eq_pairing`,
`compactPairing_swap`), the Haar Hecke algebra, its normalized indicators,
local units and corner, and the double-coset sandwich module. The route follows
Renard's argument: each statement about distributions is reduced, through the
injective density map, to the corresponding published fact about Hecke
functions. Some steps are proved directly instead.

Notation: `e = normalizedIndicator μ K hK`, `e_K = compactSubgroupHaar K hK`,
and `ctd = compactTestDensity μ`, the Haar density of a test as a compactly
supported distribution. `HeckeAlgebra μ` is the test space with multiplication
`Hecke.TestFunction.convolution μ`, and `heckeDistribution μ` is `testDensity μ`
by definition. The helper lemmas used throughout are `ctd e = e_K`
(`compactTestDensity_normalizedIndicator`) and `ctd f * ctd g = ctd (f * g)`
(`convolution_compactTestDensity`).

## Conjunct 1: `densityRealization`

Injectivity is `testDensity_injective`. The range equality holds by
extensionality: both sides are the range of the same map.

## Conjunct 2: `normalizedIndicatorRealization`

This is the helper lemma `heckeDistribution_normalizedIndicator`, the
ambient-measure/subgroup-measure comparison.

## Conjunct 3: `localUnits`

For each `T` in the finite family `s`, the proof chooses a Hecke function
`pre T` whose density is `T`. The published
`Hecke.HeckeAlgebra.finiteFamilyLocalUnits`, applied to the image family and to
`U`, gives a compact open `K ≤ U` with `e * pre T = pre T = pre T * e`. Applying
`ctd` and the two helper lemmas gives `e_K * T = T = T * e_K`.

## Conjunct 4: `idempotentOrder`

This conjunct has no ambient measure. The proof gives `G` its Borel structure
and uses Mathlib's `Measure.haar`. The lemma
`convolution_compactSubgroupHaar_compactSubgroupHaar` gives
`e_K * e_L = ctd (e^K * e^L)`.

- If `L ≤ K`, the published `normalizedIndicator_mul_of_ge` and
  `normalizedIndicator_mul_of_le` give both products equal to `e^K`.
- Conversely, `e_K * e_L = e_K` and injectivity of the density give
  `e^K * e^L = e^K`. The published `convolution_rightInvariant` shows that this
  product is right `L`-invariant, so `e^K(l) = e^K(1) ≠ 0` for `l ∈ L`. Hence
  `l ∈ K`. The nonvanishing uses `compactOpen_complex_mass_ne_zero`.

## Conjunct 5: `inversion`

- `inversionDistributions_mem_supportedOn` and
  `support_inversionDistributions_subset`: the inverted distribution is
  supported in `(support D)⁻¹`.
- `compactInversion T` is the inversion of a compactly supported `T`, with the
  compact support given by the previous lemma. It equals the actual inversion
  by definition, which supplies the required witnesses `Ti` and `Si`.
- `invFunction` precomposes a locally constant function with inversion.
  `compactSupportPairing_compactInversion` states that the extended pairing of
  `compactInversion T` with `φ` equals the pairing of `T` with `φ ∘ inv`. The
  proof compares both with a test that agrees with `φ ∘ inv` on the support of
  `T`.
- `inversionDistributions_convolution`: the published `convolution_eq_pairing`
  writes the inversion of `T * S`, evaluated on a test, as an iterated pairing. `compactPairing_swap` exchanges the
  order, and the previous lemma, applied twice together with
  `(xy)⁻¹ = y⁻¹x⁻¹`, identifies the result with the convolution of the
  inverted `S` with the inverted `T`.
- That inversion fixes `e_K` is the helper lemma
  `inversionDistributions_compactSubgroupHaar`.

## Conjunct 6: `corner`

- Lemmas `convolution_compactSubgroupHaar_compactTestDensity` and
  `convolution_compactTestDensity_compactSubgroupHaar` give
  `e_K * ctd f = ctd (e * f)` and `ctd f * e_K = ctd (f * e)`.
- `heckeDistribution_corner_mem` (the inclusion ⊆): let `f` be a corner
  element. The published `normalizedIndicator_mul_of_leftInvariant` and
  `mul_normalizedIndicator_of_rightInvariant` give `e_K * ctd f = ctd f` and
  `ctd f * e_K = ctd f`. Since `e_K` is left and right `K`-invariant, the
  helper lemmas `leftDistributions_convolution` and
  `rightDistributions_convolution` transfer that invariance to `ctd f`. The
  density is compactly supported by construction, so it lies in
  `compactDistributionsBoth K`.
- The inclusion ⊇: let `D` be compactly supported and bi-`K`-invariant. The
  helper lemmas give `e_K * D = D = D * e_K`. The published
  `convolution_testDensity_left` writes `D * e_K` as the density of
  `h0 = leftTestFunction D e`, so `ctd h0 = D`. The witness is the corner
  projection `Corner.project μ K hK h0 = e * h0 * e`, whose density is
  `e_K * D * e_K = D`.
- The unit clause is conjunct 2, since `Corner.toHeckeAlgebra 1 = e`.

## Conjunct 7: `doubleCosetBasis`

- `integral_normalizedIndicator`: `∫ e dμ = 1`.
- `sandwich_compactDirac`: `(e_K * δ_g) * e_K = ctd (e * L_g e)`. It follows
  from associativity, the helper lemma `δ_g * ctd f = ctd (L_g f)` and the
  density product lemma.
- `convolution_normalizedIndicator_leftTests`: `e * L_g e` is the mass-one
  double-coset element `Corner.massIndicator K hK μ g`. Call it `F`. It is
  bi-`K`-invariant by the published
  `convolution_mem_biInvariant_of_left_right`, so it lies in the corner. The
  integrand of `F x` vanishes unless `x ∈ KgK`, so `F` vanishes off `KgK`. The
  published `Corner.apply_eq_of_mem_doubleCosetSet` makes `F` constant on
  `KgK`, so `F = F(g) · 1_{KgK}`. Its integral is
  `∫ e · ∫ L_g e = 1`, using `HeckeAlgebra.integral_mul`, left invariance of `μ`
  and the previous lemma. Hence `F(g) · μ(KgK) = 1`, which identifies `F` with
  `massIndicator_apply` pointwise.
- `heckeDistribution_massIndicator` (first clause): combine the two previous
  lemmas.
- Basis clause: `Φ : Corner →ₗ compactDistributionsBoth K` sends `h` to the
  density of `h`. It is well defined by `heckeDistribution_corner_mem`,
  injective by `testDensity_injective` and `Corner.toHeckeAlgebra_injective`,
  and surjective by conjunct 6. The family `i ↦ massIndicator (r i)` is
  linearly independent: evaluating a vanishing finite combination at `r j`
  leaves only the `j`-th term. This uses `massIndicator_apply` and the
  uniqueness of the representative whose double coset contains `r j`; the
  nonvanishing is `doubleCosetSet_complex_mass_ne_zero`. The family spans the
  corner. The published `Corner.span_range_doubleCoset` gives spanning by all
  `doubleCoset g`. The proof rewrites `doubleCoset g` as `doubleCoset (r i)` with
  `doubleCoset_eq_of_mem`, and then as a scalar multiple of
  `massIndicator (r i)` with `doubleCoset_eq_smul_massIndicator`. The required
  basis is `(Basis.mk hli hsp).map (LinearEquiv.ofBijective Φ _)`. Its `i`-th
  vector is `e_K * δ_{r i} * e_K` by the first clause.

## Assembly

`statements` is the tuple `⟨densityRealization, normalizedIndicatorRealization,
localUnits, idempotentOrder, inversion, corner, doubleCosetBasis⟩`. The proof
uses no unimodularity, countability or other assumptions beyond those of the
published statement.
