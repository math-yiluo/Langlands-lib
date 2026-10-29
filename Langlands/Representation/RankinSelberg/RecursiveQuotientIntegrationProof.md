# Proof of normalized recursive quotient integration

Author: Worker 235.

`Langlands.RankinSelberg.recursiveQuotientIntegration` proves the published
[`RecursiveQuotientIntegrationStatement`](RecursiveQuotientIntegrationStatement.md). Its type is

```text
∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ),
  RecursiveQuotientIntegrationStatement F T n
```

with no further hypothesis. This covers every `n`, including `n = 0`, where the lower quotient
has rank one. The theorem uses only `propext`, `Classical.choice` and `Quot.sound`. It does not
assume `QuotientIwasawaIntegrationStatement`, an Iwasawa or `G = P Z K` integration formula, or a
Haar decomposition of `GL` or of the unipotent group. Every integration law it needs is proved
here, or in the helper module
[`CompactFactorizationIntegral`](../../Analysis/Local/CompactFactorizationIntegral.md), or is
already published.

All auxiliary declarations are in the namespace `Langlands.RankinSelberg.RecursiveIntegration`.
They are internal steps of this proof and are derived results, not literature claims.

## Notation

Write `G = GL_(n+2)(F)`, `G' = GL_(n+1)(F)`, `N = N_(n+2)` and `N' = N_(n+1)` for the
upper-unipotent subgroups, and `V = F^(n+1)` for columns. Write `ι(g) = rankInclusion 1 g` for
`diag(g, 1)`, and `col w` for the published radical matrix `[[I, w], [0, 1]]` (`LastRowReduction.col`).
`K` is `Conductor.integralSubgroup (ValuativeRel.valuation F).integer (n+1)`, `K'` is the rank
`n+1` version, and `O` is the valuation ring. The measures are `μG = generalLinearHaar F (n+1)`,
`μG' = generalLinearHaar F n`, `μN = unipotentHaar F (n+1)`, `μN' = unipotentHaar F n` and
`dMult = localMultiplicativeHaar F`.

## Route

Let `ν` be the right side of the statement:
`map coordinates ((μsmall × (dMult × μG|K)).withDensity weight)`.

1. The rank `n+2` unipotent Haar measure is the image of `columnHaar × μN'` under
   `(w, u) ↦ col w · ι(u)`, with constant one.
2. Haar measure on `G` is recovered from the parabolic coordinates `(a, g, w) ↦ ι(g) col(w) a`
   and from `μG` restricted to `K`. This is the factorization integral of the helper module,
   applied to the Iwasawa decomposition `G = P K`. The mass of the integral points is one.
3. For `0 ≤ f` in `C_c(G, ℝ)`, define the column integral
   `h_x(g) = ∫ f(ι(g) col(w) x) dw`. It is continuous with compact support on `G'`. The weight
   times the `N`-average of `f` at `[ι(g) x]` equals the `N'`-average of `h_x` at `[g]`.
4. The Weil formula of `μsmall` (from its compatibility) and steps 1–3 give the lower-integral
   identity
   `∫⁻ ofReal(avg_N f) dν = ∫⁻ ofReal(f) dμG`.
5. Step 4 shows that `ν` is finite on compact sets, hence regular. The compatibility of `μlarge`
   gives the same identity for `μlarge`. Every nonnegative compactly supported continuous function
   on `N \ G` is an average `avg_N f` (published positive lifting). The Riesz–Markov–Kakutani
   uniqueness theorem then gives `μlarge = ν`.

The source formula is JPSS 1983, Section 8.3, printed p449, equation (1), as cited in the statement
Markdown. The Lean proof does not follow a written proof from the source, which only recalls the
formula. It uses the derivation sketched in the statement Markdown: the factorization `G = P Z K`
and the left Haar measure of the mirabolic in affine coordinates. The constant is fixed directly
by the mass-one normalizations, not by a separate test on `K`.

## Section `Algebra` (any field `K`)

- `parabolicPoint x = ι(x.2.1) * col x.2.2 * scalar x.1` for
  `x : Kˣ × (GL_(n+1)(K) × K^(n+1))`.
- `parabolicShift x₀ x = (x₀.1⁻¹ x.1, x₀.2.1⁻¹ x.2.1, -((x.2.1⁻¹ x₀.2.1) x₀.2.2) + x.2.2)`.
- `scalar_mul_comm`: scalar matrices commute with everything
  (`Matrix.GeneralLinearGroup.scalar_commute`).
- `parabolicPoint_mul_shift` and `parabolicPoint_shift`:
  `parabolicPoint (parabolicShift x₀ x) = (parabolicPoint x₀)⁻¹ * parabolicPoint x`. The proof
  moves the scalar to the right and uses `col_mul_rankInclusion`, `col_add` and `col_neg`.
- `exists_parabolicPoint_eq`: a matrix whose last row is `(0, …, 0, d)` is a `parabolicPoint`.
  Its entry `d` is nonzero, because otherwise the last row vanishes and the determinant is zero.
  Then `b * scalar d⁻¹` lies in the mirabolic group, and `eq_radicalElement_mul_levi` writes it as
  `col v * ι(g)`. Finally `col v * ι(g) = ι(g) * col(g⁻¹ v)`.

Subsection `Integral`, for a subring `O`:

- `mulVec_mem`: an integral matrix maps integral columns to integral columns.
- `affineMatrix_entries_mem`: the entries of `affineMatrix A v` (that is `col v * ι(A)`) lie in `O`
  if and only if those of `A` and of `v` do. The proof is by cases on the last row and column,
  using `affineMatrix_first`, `affineMatrix_last` and `affineMatrix_bottom`.
- `affineMatrix_one_zero` and `affineMatrix_inv`:
  `(affineMatrix A v)⁻¹ = affineMatrix A⁻¹ (-(A⁻¹ v))`, from `affineMatrix_mul`.
- `col_mul_rankInclusion_mem_iff`: `col v * ι(A) ∈ integralSubgroup O (n+1)` if and only if
  `A ∈ integralSubgroup O n` and `v` is integral. Both directions use the entry criterion
  `Conductor.mem_integralSubgroup` for the matrix and its inverse.
- `scalar_mem_integralSubgroup`: the scalar matrix of an integral unit is integral.
- `mul_scalar_mem_iff`: for `m` in the mirabolic group, `m * scalar a` is integral if and only if
  `a ∈ integralUnits O` and `m` is integral. The last diagonal entries of `m * scalar a` and of its
  inverse are `a` and `a⁻¹`.
- `parabolicPoint_mem_iff`: `parabolicPoint (a, g, w)` is integral if and only if `a` is an
  integral unit, `g ∈ integralSubgroup O n` and `w` is integral. The proof uses
  `ι(g) col(w) = col(g w) ι(g)`.

## Section `Topology`

- `continuous_parabolicPoint` and `continuous_parabolicShift`.
- `shearHomeomorph : (g, w) ↦ (g, g w)`, a homeomorphism of `GL_(n+1) × K^(n+1)`.
- `isClosedEmbedding_rankInclusion_mul_col` (for Hausdorff `K`): `(g, w) ↦ ι(g) col(w)` is a closed
  embedding. It is the composite of the shear, the published `affineHomeomorph.symm` and the
  inclusion of the closed mirabolic subgroup (`Mirabolic.isClosed`).

## Sections `Support`, `Weil`, `Factorization`

- `continuous_hasCompactSupport_integral`: if `Φ` is continuous with compact support on `X × Y`,
  then `x ↦ ∫ Φ(x, y) dμ` is continuous with compact support. The integral is a set integral over
  the compact projection of the support, so `continuous_parametric_integral_of_continuous`
  applies. The support lies in the other projection.
- `lintegral_quotientAverageReal`: for a compatible quotient measure `ν` and `0 ≤ h` continuous with
  compact support, `∫⁻ ofReal(avg_H h) dν = ∫⁻ ofReal(h) dμG`. It comes from the complex fields
  `averaging_integrable` and `integral_formula` of `IsCompatible`, through `quotientAverage_ofReal`
  and `ofReal_integral_eq_lintegral_ofReal`.
- `exists_parabolicPoint_mul`: for a valuation `v`, every `y ∈ GL_(n+2)` is
  `parabolicPoint x₀ * k₀` with `k₀ ∈ integralSubgroup v.integer (n+1)`. This is the published
  `Iwasawa.exists_upperTriangular_mul` followed by `exists_parabolicPoint_eq`.

## Section `Measure` (any nonarchimedean local field with Hausdorff, second countable topology)

Private instances supply local compactness and second countability of matrix groups, unipotent
subgroups, `Fˣ` and the quotients, from the field topology.

- `columnIntegers F n`: the compact open set `O^(n+1)` as a `PositiveCompacts`, with
  `mem_columnIntegers` and `isOpen_columnIntegers`.
- `columnHaar F n = addHaarMeasure (columnIntegers F n)`: additive Haar measure on `F^(n+1)` giving
  `O^(n+1)` mass one (`columnHaar_integers`). The instance `columnHaar_isAddHaar` records that it
  is an additive Haar measure.
- `mem_levelOpenSubgroup_zero`: level zero is the integral subgroup (`levelSubgroup_zero`).
- `coordinateMeasure_columnHaar`: assuming the determinant law
  `hdet : (columnHaar F n).map (toLin' M) = (χ (det M))⁻¹ • columnHaar F n`, the published
  `LastRowReduction.coordinateMeasure (columnHaar F n) μN'` equals `μN`. The published
  `exists_coordinateMeasure_eq_smul` gives `κ • μN`. Evaluate on the integral points
  `unipotentIntegralOpen F (n+1)`: by `col_mul_rankInclusion_mem_iff` their preimage is
  `O^(n+1) × N'(O)`, of mass `1 · 1`, while `μN` gives them mass one. Hence `κ = 1`.
- `lintegral_col_mul_rankInclusion`: under the same determinant law,
  `(χ(det g))⁻¹ ∫⁻ Φ(col v · ι(g)) dv = ∫⁻ Φ(ι(g) · col w) dw`. Substitute
  `col v · ι(g) = ι(g) · col(g⁻¹ v)` and use the law for `M = g⁻¹`.
- `measurePreserving_parabolicShift`: `parabolicShift x₀` preserves `dMult × (μG' × dw)` for any
  left-invariant `dMult`, `μG'` and additive-invariant `dw`. In the `(g, w)` factor it is a skew
  product, `g ↦ g₀⁻¹ g` followed by a translation in `w` that depends on `g`
  (`MeasurePreserving.skew_product`, `map_add_left_eq_self`). In `a` it is left translation.
- `measure_parabolicPoint_preimage`: the preimage of `K` under `parabolicPoint` is
  `integralUnits × (K' × O^(n+1))`, by `parabolicPoint_mem_iff`, and its
  `localMultiplicativeHaar × (μG' × columnHaar)` measure is `1 · 1 · 1`.
- `hasCompactSupport_slice`: slices of compactly supported functions on products are compactly
  supported.

Section `Pointwise`, for a function `f` on `GL_(n+2)` and `x ∈ GL_(n+2)`:

- `columnIntegrand f x (g, w) = f(ι(g) col(w) x)` and `columnIntegral f x g = ∫ columnIntegrand f x
  (g, w) d(columnHaar)`. The integrand is a named definition. Stating the slices through it avoids
  an expensive unification of mixed `n + 2` and `n + 1 + 1` matrix products.
- `continuous_columnIntegrand`, `continuous_columnIntegrand_joint` (jointly in `x`) and
  `hasCompactSupport_columnIntegrand`. The last pulls back the support of `f` by the closed
  embedding `isClosedEmbedding_rankInclusion_mul_col` and right translation by `x`.
- `columnIntegral_continuous_hasCompactSupport`: from `continuous_hasCompactSupport_integral`.
- `ofReal_columnIntegral`: for `f ≥ 0`, `ofReal (columnIntegral f x g)` is the lower integral of
  `ofReal ∘ columnIntegrand`.
- `ofReal_integral_unipotentHaar`: for `f ≥ 0` continuous with compact support,
  `ofReal(∫_N f(u y) du) = ∫⁻_{N'} ∫⁻_V ofReal f(col v · ι(u) · y) dv du`. This uses
  `coordinateMeasure_columnHaar`, `lintegral_map` and `lintegral_prod_symm'`.
- `inv_mul_ofReal_average`: the pointwise identity
  `(χ(det g))⁻¹ · ofReal(∫_N f(u ι(g) x) du) = ofReal(∫_{N'} columnIntegral f x (u g) du)`.
  Expand both sides as lower integrals. For each `u ∈ N'`, apply `lintegral_col_mul_rankInclusion`
  to `u g`. Then `det(u g) = det g` (`unipotent_det`) and `ι(u g) = ι(u) ι(g)`.
- `exists_nonneg_average_eq`: every nonnegative `φ ∈ C_c(N \ G, ℝ)` is `avg_N f` for some
  nonnegative `f ∈ C_c(G, ℝ)` (the published `realQuotientPositiveLifting`).

Section `Main`, with Borel structures on all groups and quotients:

- `lintegral_ofReal_average_map`. Hypotheses: `χ : F →*₀ ℝ≥0`, an absolute value `abv` with
  `abv x = χ x` that is continuous, the determinant law `hdet` for `columnHaar`, the two
  right-invariance instances, and a compatible `μsmall`. Conclusion: for every `f ∈ C_c(G, ℝ)`
  with `f ≥ 0`, `∫⁻ ofReal(avg_N f) dν = ∫⁻ ofReal(f) dμG`, with `weight` built from `abv`. The proof
  is a chain of equalities:
  1. Unfold `ν` with `lintegral_map` and `lintegral_withDensity_eq_lintegral_mul`. Continuity of
     the weight comes from continuity of `abv ∘ det` and positivity of
     `quotientDeterminantAbs`. Continuity of the average is the published
     `continuous_quotientAverageReal`, and continuity of the coordinates is
     `continuous_recursiveQuotientCoordinates`.
  2. Integrate over `μsmall` innermost (`lintegral_prod_symm`).
  3. For fixed `(a, k)`, at `[g]` the integrand is
     `(χ(det g))⁻¹ · ofReal(avg_N f [ι(g) · (scalar a · k)])`
     (`recursiveQuotientCoordinates_mk`, `quotientDeterminantAbs_mk`). By `inv_mul_ofReal_average`
     it equals `ofReal(avg_{N'} h)` with `h = columnIntegral f (scalar a · k)`. Apply
     `lintegral_quotientAverageReal` to `μsmall`, then `ofReal_columnIntegral`.
  4. Put `k` outermost (`lintegral_prod_symm`), and recombine `(a, g, w)` into one integral over
     `dMult × (μG' × columnHaar)`, using `parabolicPoint (a, g, w) * k = ι(g) col(w) (scalar a · k)`.
  5. Apply `CompactFactorization.lintegral_restrict_lintegral_mul` with `ι = parabolicPoint`.
     Factorization comes from `exists_parabolicPoint_mul`, translations from
     `measurePreserving_parabolicShift` and `parabolicPoint_shift`, and the mass factor from
     `measure_parabolicPoint_preimage`, which equals one.
- `eq_map_recursiveQuotientCoordinates`: with the same `χ`, `abv` and `hdet`, every pair of
  compatible `μsmall` and `μlarge` satisfies `μlarge = ν`. Proof:
  - `ν` is finite on compact sets. For compact `C`, Urysohn's lemma
    (`exists_continuous_one_zero_of_isCompact`) gives `u ∈ C_c` with `0 ≤ u ≤ 1` and `u = 1` on
    `C`. Write `u = avg_N f` with `f ≥ 0` (`exists_nonneg_average_eq`). Then
    `ν C ≤ ∫⁻ ofReal(avg_N f) dν = ∫⁻ ofReal f dμG < ∞`.
  - The quotient is Hausdorff (`leftQuotient_t2Space`), locally compact and second countable, hence
    metrizable and σ-compact. So `ν` is regular (`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`).
    `μlarge` is regular by compatibility.
  - `Measure.ext_of_integral_eq_on_compactlySupported_nnreal`. For `φ ∈ C_c(N \ G, ℝ≥0)`, write
    `φ = avg_N f` with `f ≥ 0`. For both measures, `∫ φ = (∫⁻ ofReal(avg_N f)).toReal`
    (`integral_eq_lintegral_of_nonneg_ae`), and this equals `(∫⁻ ofReal f dμG).toReal`, by
    `lintegral_ofReal_average_map` for `ν` and by `lintegral_quotientAverageReal` for `μlarge`.

## The final theorem

`recursiveQuotientIntegration F T n` installs the topology, valuation and local-field structure of
`T`, the Hausdorff and second-countability certificates `T.fieldT2` and `T.secondCountableTopology`,
and the same Borel structures as the statement, plus a Borel structure on `F.Carrier` that is used
only for `columnHaar`. It then introduces the two right-invariance instances, `μsmall`, `μlarge`
and their compatibility hypotheses. It applies `eq_map_recursiveQuotientCoordinates` with
`χ = T.normalizedAbsHom` and `abv = normalizedAbsoluteValue T`. These agree by definition, and
`abv` is continuous by `T.continuous_normalizedAbsHom`. The determinant law `hdet` is the published
`HarmonicAnalysis.haarMeasure_map_matrix`, with the scalar law `padicScalarHaarScaling` for the
additive Haar measure of `F`.

## Scope

The final theorem is exactly the published statement: no hypothesis is added, no published file is
changed, and its constant is one. The general-field theorems keep `χ`, `abv` and the determinant
law as explicit hypotheses; the final theorem discharges them with published p-adic results. The
proof establishes no Iwasawa formula for the full torus, and it does not use the related
`QuotientIwasawaIntegrationStatement`.
