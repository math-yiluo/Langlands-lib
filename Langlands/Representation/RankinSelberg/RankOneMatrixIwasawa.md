# Iwasawa integration on `GL_(n+1)` with a rank-one torus coordinate

Module `Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa`, namespace
`Langlands.RankinSelberg.RankOneIwasawa`. This is a helper module of the positive-rank
branch of the proof of `RankOneMatrixWhittakerComparisonStatement`.

## Result

Let `F` be a `p`-adic field with its canonical topology, valuation and local-field
structure. Let `G = GL_(n+1)(F)`, `K = GL_(n+1)(O)`, and let `N` be the upper unipotent
group. Matrix groups and `Fˣ` carry their Borel σ-algebras. The parameter space is
`X = (GL₁ × (Fˣ)ⁿ) × N`. A parameter `((g, a), u)` gives the point

`point((g, a), u) = u · diag(det g / ∏ aᵢ, a₁, …, aₙ)`.

The diagonal is `torusCoord n (g, a) = Fin.cons (det g · (∏ a)⁻¹) a`. This is a group
homomorphism `GL₁ × (Fˣ)ⁿ → (Fˣ)^(n+1)` with section `torusSection`. The measure on
`X` is `iwasawaMeasure F n = parameterMeasure F n × unipotentHaar F n`. Here
`parameterMeasure F n` is the product of `generalLinearHaar F 0` (normalized by
`GL₁(O)` of mass one) and `Measure.pi` of `localMultiplicativeHaar F` (normalized by
`O^×` of mass one), with density `weight F n`. The density is
`ω(b) = δ(torusCoord b)⁻¹`, where `torusModulus F m t = δ(t) = ∏_{i<j} |tᵢ| / |tⱼ|`
is the published Levi modulus `leviModulus (singletons m)` of the singleton blocks.

The main theorem `map_iwasawaMeasure_prod` states that

`Measure.map (fun (x, k) ↦ point x * k) (iwasawaMeasure F n × (generalLinearHaar F n)|_K)
  = generalLinearHaar F n`.

So `∫_G f dg = ∫_K ∫_X f(u · D(b) · k) δ(D(b))⁻¹ du db dk` holds for every measurable
`f`, and the constant is exactly one. No compact support or continuity is required.

## Proof

The proof applies the Library factorization integral
`CompactFactorization.lintegral_restrict_lintegral_mul` to the map `point`, the subgroup
`K` and the measure `iwasawaMeasure F n`. It needs three inputs.

1. **Factorization** (`exists_point_mul`). Every `y ∈ G` is `point x * k` with `k ∈ K`.
   `Iwasawa.exists_upperTriangular_mul` writes `y = b k` with `b` upper triangular.
   Then `u = b · diag(bᵢᵢ)⁻¹` is unipotent and `x = (torusSection (bᵢᵢ), u)`.
2. **Translation** (`shift`, `point_shift`, `measurePreserving_shift`). For each `x₀`,
   `shift x₀ (b, u) = (b₀⁻¹ b, D(t₀)⁻¹ (u₀⁻¹ u) D(t₀))`, with `t₀ = torusCoord b₀`,
   satisfies `point (shift x₀ x) = (point x₀)⁻¹ * point x`. It preserves
   `iwasawaMeasure F n` for the following reasons.
   - Left translation by `b₀⁻¹` multiplies the density measure by `ω(b₀)`. This is
     `map_mul_left_withDensity`, for a left-invariant measure with a multiplicative
     density.
   - Conjugation `diagonalConj` by the diagonal matrix `D(t₀)⁻¹` multiplies
     `unipotentHaar` by `δ(t₀⁻¹)⁻¹ = δ(t₀)`. The declaration is imported from
     [DiagonalUnipotentHaar](DiagonalUnipotentHaar.md), together with its matrix
     and continuity identities. `unipotentConj_map` specializes the shared
     `diagonalConj_map` theorem to the canonical topological data.
   - The two scalars `ω(b₀) = δ(t₀)⁻¹` and `δ(t₀)` cancel. `Measure.map_prod_map`
     combines the two factors.
3. **Mass one** (`iwasawaMeasure_point_preimage`). By `point_mem_integralSubgroup_iff`,
   an upper triangular point lies in `K` exactly when its diagonal consists of
   valuation-one units and its unipotent part is integral. This uses
   `Iwasawa.valuation_diag_eq_one` and `Iwasawa.diagonalUnits_mem`. By
   `torusCoord_valuation_iff` and `mem_integralSubgroup_zero_iff`, the preimage of `K`
   is `(GL₁(O) × (O^×)ⁿ) × N(O)`. The density is one there (`torusModulus_eq_one`), and
   each factor has mass one.

The measure identity then follows by evaluating both sides on measurable sets, using
`Measure.prod_apply_symm` and indicator functions.

## Unfolded form

`map_unfoldedMeasure` restates the formula with the variables reordered for later
Fubini arguments:

`Measure.map unfoldedPoint (unfoldedMeasure F n) = generalLinearHaar F n`.

Here `unfoldedMeasure F n = (glOneMeasure F n × (tailMeasure F n × dk|_K)) × du` and
`unfoldedPoint ((g, (a, k)), u) = u · diag(det g / ∏ a, a) · k`. The measures are
`glOneMeasure F n = |det g|⁻ⁿ dg` on `GL₁` (density `ω(g, 1)`) and
`tailMeasure F n = ω(1, a) da` on `(Fˣ)ⁿ`. `parameterMeasure_eq_prod` splits the density
by `weight_split` and `prod_withDensity`. The reordering is a composite of
`measurePreserving_prodAssoc` and `Measure.measurePreserving_swap`, so `map_unfoldedMeasure`
follows from `map_iwasawaMeasure_prod`.

## Auxiliary facts used later

- `weight_split`: `ω(g, a) = ω(g, 1) · ω(1, a)`.
- `weight_glOne`: `ω(g, 1) = (|det g|ⁿ)⁻¹`, from `torusModulus_cons_one`:
  `δ(diag(x, 1, …, 1)) = |x|ⁿ`.
- `det_point`: `det (point ((g, a), u)) = det g`.
- Continuity of `torusCoord`, `torusModulus`, `weight` and `point`, and the
  σ-finiteness and s-finiteness instances of the parameter measures.

## Provenance and scope

The parametrization by `GL₁ × (Fˣ)ⁿ`, rather than by the full torus, is internal to
this proof. It makes `|det|` of a point equal to `|det g|` of its `GL₁` coordinate.
The positive-rank comparison integrates over that coordinate (the JPSS variable of
`Ψ(s, W)`). The formula is the standard Iwasawa integration formula
`dg = δ(a)⁻¹ du da dk` with the Library normalizations. The module assumes nothing and
uses no regularity or quotient-measure theorem.
