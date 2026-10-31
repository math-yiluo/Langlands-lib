# Proof of full rectangular Schwartz Fourier covariance

`Langlands.HarmonicAnalysis.rectangularFourierCovariance` proves the closed
proposition
[`RectangularFourierCovarianceStatement.{uK}`](RectangularFourierCovarianceStatement.md)
exactly. It uses only that proposition's hypotheses: the field telescope, a
unitary additive character `ψ`, a supplied additive Haar measure `μ`, ranks
`r s : ℕ` and the scalar self-duality proof `hsd : IsSelfDual ψ μ`. It adds no
premise. Write `Δ = MeasureTheory.distribHaarChar K` and
`ν = Langlands.RankinSelberg.rectangularMeasure μ r s`, the nested product of
`r` copies of the product of `s` copies of `μ.measure`.

The proof is the change of variables `z = y g` in the Fourier integral. The
published determinant change of variables `haarMeasure_map_rectangular` (from
[`PadicRectangularHaarScalingProof`](PadicRectangularHaarScalingProof.md))
needs two instances that the statement does not supply. It needs a Borel
structure on the matrix space, which is a product of copies of `K`, and it
needs `ν` to be an additive Haar measure. The proof derives both from the
hypotheses. Sigma-finiteness of `μ.measure` comes from the published
`selfDualSigmaFinite`, and Mathlib then shows that the finite product `ν` is an
additive Haar measure. Second countability of `K` is derived from
self-duality in the first section below. Mathlib then shows that the product
sigma-algebra on the matrix space is its Borel sigma-algebra.

## Second countability of the field

`secondCountableTopology_of_isSelfDual` assumes the full telescope of the
statement and `IsSelfDual ψ μ`, and proves `SecondCountableTopology K`. It
splits on whether `{0}` is open.

**Discrete case.** If `{0}` is open, the published
`isFiniteMeasure_of_isSelfDual_of_isOpen_singleton_zero` shows that
`μ.measure` is finite, and `K` is discrete. If `K` were not compact, Mathlib's
`measure_univ_of_isAddLeftInvariant` would give `μ.measure univ = ∞`, which
contradicts finiteness. So `K` is compact and discrete, hence finite, and a
finite discrete space is second countable.

**Nondiscrete case.** If `{0}` is not open, the punctured neighbourhood filter
`𝓝[≠] 0` is nontrivial. The published `sigmaCompactSpace_of_addHaar` makes `K`
sigma-compact. The new lemma `nhds_zero_isCountablyGenerated_of_addHaar` gives
`0` a countable neighbourhood basis. The general lemma
`secondCountableTopology_of_nhds_zero_isCountablyGenerated` then concludes.

`nhds_zero_isCountablyGenerated_of_addHaar` assumes only a locally compact
Hausdorff topological ring `K` whose underlying ring is a field, its Borel
sets, a regular additive Haar measure `μ` and nontriviality of `𝓝[≠] 0`. It
uses neither self-duality nor total disconnectedness. The scaling law is
Mathlib's `distribHaarChar_mul`, `Δ a * μ E = μ (a • E)`. Its first three steps
follow steps 1–3 of the nondiscrete case of the published
[`SelfDualSigmaFiniteProof`](SelfDualSigmaFiniteProof.md), in the same order.
Step 4 is new.

1. Choose a compact neighbourhood `V` of `0`. Its measure is finite and
   nonzero. Pick an interior point `p ≠ 0` of `V`, and separate `0` from `p`
   by disjoint open sets `U ∋ 0` and `O ∋ p`. Then `V \ O` is a neighbourhood
   of `0` with `μ (V \ O) < μ V`.
2. By the tube lemma there is a nonzero `b` with `b * v ∈ V \ O` for every
   `v ∈ V`. For the unit `u = b` this gives `u • V ⊆ V \ O`, hence `Δ u < 1`.
3. The compact sets `S n = u ^ n • V` decrease, and their intersection lies in
   `{0}`. Suppose `x ≠ 0` lies in every `S n`, and let `w` be the unit `x`.
   Then `((u ^ n)⁻¹ * w) • V ⊆ V * V`, so `Δ w * μ V ≤ Δ u ^ n * μ (V * V)` for
   every `n`. The right side tends to `0`, but the left side is positive.
4. Each `S n` is a neighbourhood of `0`, since it is the image of the
   neighbourhood `V` of `0` under multiplication by a unit
   (`smul_mem_nhds_smul_iff`). Let `t` be a neighbourhood of `0`. It is then a
   neighbourhood of `⋂ n, S n ⊆ {0}`. A decreasing family of compact sets
   eventually lies inside every neighbourhood of its intersection
   (`exists_subset_nhds_of_isCompact`), so `S n ⊆ t` for some `n`. Hence the
   sets `S n` form a countable basis of `𝓝 0`.

`secondCountableTopology_of_nhds_zero_isCountablyGenerated` is a general fact
about a sigma-compact commutative topological additive group `G` whose
neighbourhood filter at `0` is countably generated. It equips `G` with its
right uniformity, for which `G` is a uniform additive group
(`isUniformAddGroup_of_addCommGroup`). The uniformity is then countably
generated (`IsUniformAddGroup.uniformity_countably_generated`), so `G` is
pseudometrizable. Mathlib's `EMetric.secondCountable_of_sigmaCompact` then
shows that `G` is second countable. The auxiliary uniform and metric
structures exist only inside this proof. The conclusion concerns the given
topology.

## Scalar change of variables

`map_mul_left_eq_inv_distribHaarChar` states that, for a regular additive Haar
measure `ν` on `K` and a unit `a`, the pushforward of `ν` under `x ↦ a * x` is
`(Δ a)⁻¹ • ν`. On a measurable set `t`, the preimage of `t` under this map is
`a⁻¹ • t`. So the pushforward has value `ν (a⁻¹ • t) = Δ (a⁻¹) * ν t` there, by
`distribHaarChar_mul`, and `Δ (a⁻¹) = (Δ a)⁻¹`.

## Change of variables for the nested product measure

`rectangularMeasure_map_mul_right` assumes `SecondCountableTopology K` and
`SigmaFinite μ.measure` in addition to the scalar telescope. For
`g : GeneralLinear s K` it proves

```text
(rectangularMeasure μ r s).map (fun m => m * g.val) =
  ((Δ (GeneralLinear.determinant g)) ^ r)⁻¹ • rectangularMeasure μ r s.
```

The published `haarMeasure_map_rectangular` takes a monoid-with-zero hom
`χ : K →*₀ ℝ≥0` with the scalar law `ν.map (a * ·) = (χ a)⁻¹ • ν` for all
`a ≠ 0`. The proof lets `χ` be the extension of `Δ` by `χ 0 = 0`, so
`χ x = Δ x` for `x ≠ 0`. The previous section gives the scalar law for
`μ.measure`. The theorem is applied to `ν` with left factor `A = 1` and right
factor `B = g.val`. It gives the factor
`(χ (det 1) ^ s * χ (det g.val) ^ r)⁻¹`, where the exponent of the right factor
is the number `r` of rows. This simplifies to `(Δ (det g) ^ r)⁻¹`. The
required instances are those described at the start: `ν` is an additive Haar
measure because `μ.measure` is sigma-finite, and the product sigma-algebra is
Borel because `K` is second countable. The proof makes no case distinction on
the ranks.

## The Fourier integral

The main theorem first derives `SigmaFinite μ.measure` from
`selfDualSigmaFinite` and `SecondCountableTopology K` from
`secondCountableTopology_of_isSelfDual`. It then restates the pushforward law
above for the published homeomorphism `rectangularLeftRightHomeomorph 1 g`,
whose underlying map is `m ↦ m * g.val`.

Both sides are Schwartz–Bruhat functions, and the proof compares their values
at every matrix `b`. `rectangularFourierEquiv_apply` turns both sides into
values of the plus-sign raw integral `rectangularFourierIntegral` against the
actual measure `ν`. The left side is the raw integral of
`rectangularTranslate g Φ` at `b`. The right side is `c` times the raw
integral of `Φ` at `b * (inverseTranspose s K g).val`, where
`c = ((Δ (det g) : ℂ) ^ r)⁻¹`.

The published `rectangularFourierIntegral_leftRight` (from
[`RankOneMatrixFunctionalEquationComparisonFourierTransport`](../Representation/RankinSelberg/RankOneMatrixFunctionalEquationComparisonFourierTransport.md))
turns an exact pushforward law into a Fourier change of variables. It is
applied with `A = 1`, `B = g` and the factor `(Δ (det g) ^ r)⁻¹`. It states
that the Fourier integral of `y ↦ Φ (1 * y * g.val)` at `b` equals that factor
times the Fourier integral of `Φ` at
`(inverseTranspose r K 1).val * b * (inverseTranspose s K g).val`. Its proof
applies the change of variables `z = y g` to the integral, and then moves the
factor `g⁻¹` across the unsigned entry pairing by transposition. Removing the
identity factors (`inverseTranspose r K 1 = 1`) gives the right side of the
statement. Finally, the coercion of the factor from `ℝ≥0` to `ℂ` is
rewritten as `((Δ (det g) : ℝ) : ℂ) ^ r` inverted in `ℂ`.

## Provenance

The law proved here is the derived generic formulation of the unnumbered
covariance formula after formula (6) in H. Jacquet, I. I. Piatetski-Shapiro
and J. A. Shalika, *Rankin-Selberg Convolutions*, American Journal of
Mathematics 105 (1983), 367–464, Section 6.1, printed page 428 (registered as
`jpss-1983-rankin-selberg`). The statement's Markdown records the
exact correspondence and the formal generalizations: arbitrary ranks, the
generic field telescope, and the intrinsic character `Δ` in place of
`|det g|`. The present proof does not identify `Δ` with a normalized absolute
value.

The route of the proof is internal, derived content. It follows the
change-of-variables sketch in the statement's Markdown. Second countability,
the scalar change of variables and the passage from `Δ` to `χ` are new
arguments of this module. The countable basis argument reuses the dilation
construction of `SelfDualSigmaFiniteProof`, as described above. The
determinant change of variables, the Fourier transport lemma, sigma-finiteness
and the discrete-case finiteness are published Library results, used without
change.
