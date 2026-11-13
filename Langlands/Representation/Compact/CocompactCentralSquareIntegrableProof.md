# Renard IV.3.3, Remark: integrals over `G/A` for a cocompact central subgroup

Author: Worker 27.

The theorem
`Langlands.Renard.CompactRepresentation.cocompactCentralSquareIntegrable`
proves the published proposition
`Langlands.Renard.CompactRepresentation.CocompactCentralSquareIntegrableStatements`
exactly as stated. It keeps the independent group and carrier universes `u v`
and adds no hypothesis. The statement's Lean/Markdown pair and its imports are
unchanged.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.3.3, Remark, printed p.102 / PDF p.108.
The results it extends are IV.3.2 Proposition and Lemma and IV.3.3 Lemma and
Corollary, printed pp.100–102 / PDF pp.106–108. Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Route

Renard only remarks that the results stay valid. The Lean proof does not
re-run the IV.3.2–IV.3.3 arguments over `G/A`. It moves every integral over
`G/A` to `G/Z(G)` along the projection
`pr = centralQuotientProjection A hA : G/A → G/Z(G)` (from
`Langlands.Representation.Plancherel.CentralSubgroupCoefficients`), using the
pushforward measure `ν = μ.map pr`. It then applies the published `G/Z(G)`
theorems `essentiallySquareIntegrableAdmissible`,
`squareIntegrableUnitarySemisimple` and `schurOrthogonality` to `ν`. Those
theorems allow an arbitrary Haar measure on `G/Z(G)` that is also right
invariant. So the route needs no comparison between `ν` and the given `μZ` for
items 2–5. Only item 1 compares `μZ` with `ν`.

The hypothesis `IsClosed A` is not used.

## Part A: comparing two Haar measures (section `HaarComparison`)

Here `H` is a topological group with Borel σ-algebra, and `K ≤ H` is a compact
open subgroup.

* `isCompact_of_mul_right_mem_of_measure_ne_top`: suppose a set `S` is stable
  under right multiplication by `K` and has finite measure for some Haar
  measure. Then `S` is a union of left cosets `qK`. Each coset has the
  positive measure `m K`, by left invariance (`measure_preimage_mul`). An
  infinite family of these disjoint cosets inside `S` would give `S` infinite
  measure (`ENNReal.tsum_const_eq_top_of_ne_zero`). So `S` is a finite union of
  compact cosets and is therefore compact.
* `lintegral_ofReal_eq_of_mul_right_invariant`: let `f ≥ 0` be measurable and
  right `K`-invariant, with finite lower integral for `m₁`. For `t > 0`, the
  superlevel set `{t < f}` has finite `m₁`-measure by Markov's inequality
  (`meas_ge_le_lintegral_div`). It is right `K`-invariant, so it is compact by
  the previous lemma. On compact sets Mathlib's
  `Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure` gives
  `m₂ = haarScalarFactor m₂ m₁ • m₁`. That lemma assumes no regularity of the
  Haar measures. The layer-cake formula `lintegral_eq_lintegral_meas_lt` then
  gives `∫⁻ f dm₂ = c · ∫⁻ f dm₁` with the finite constant
  `c = haarScalarFactor m₂ m₁`.
* `integrable_of_mul_right_invariant`: for a continuous, nonnegative, right
  `K`-invariant real function, integrability for `m₁` implies integrability
  for `m₂`.

## Part B: the pushforward measure (section `Pushforward`)

* `exists_isCompact_image_superset`: in a locally compact group, every compact
  subset of `G/N` lies in the image of a compact subset of `G`. The proof
  covers the compact set by images of interiors of compact neighbourhoods. It
  uses the fact that the quotient map is open.
* `isCompact_image_center`: the image of `Z(G)` in `G/A` is the range of the
  continuous map `Z(G)/(A ∩ Z(G)) → G/A`. Its domain is compact by
  hypothesis, so the image is compact.
* `tendsto_centralQuotientProjection_cocompact`: `pr` is proper. Let
  `C ⊆ G/Z(G)` be compact, with `C ⊆ mk(D)` for a compact `D ⊆ G`. The
  preimage `pr⁻¹(C)` lies in the compact product set `mk_A(D) · mk_A(Z(G))`.
* `isHaarMeasure_map_centralQuotientProjection`: `pr` is a continuous,
  surjective, proper homomorphism, so Mathlib's `Measure.isHaarMeasure_map`
  makes `ν` a Haar measure.
* `isMulRightInvariant_map_centralQuotientProjection`: `ν` is right invariant.
  The proof writes each right translation on `G/Z(G)` as the image of a right
  translation on `G/A` and uses `map_mul_right_eq_self` for `μ`.

## Part C: the main theorem (section `Main` and `cocompactCentralSquareIntegrable`)

Helper lemmas:

* `nonempty_unitaryCentralCharacter`: the statement's central-character
  hypothesis is a unitary `χ : Z(G) →* ℂˣ` by which the centre acts. The
  published `UnitaryCentralCharacter` also asks that `ker χ` be open. For a
  smooth representation with a nonzero vector `v`, `ker χ` contains the open
  subgroup `Z(G) ∩ Stab(v)`, so it is open (`Subgroup.isOpen_mono`). On the zero
  representation the trivial character works.
* `exists_compactOpen_coefficientNorm_invariant`: let `L` be a compact open
  subgroup of `G` fixing `x`; it exists by van Dantzig cofinality. Its image in
  `G/Z(G)` is a compact open subgroup. The descended coefficient norm
  `c.coefficientNorm ℓ x` is right invariant under that subgroup.
* `exists_memLp_map_of_squareIntegrable`: this turns the statement's predicate
  `SqIntModA` into the `G/Z(G)` hypothesis for `ν`. The function
  `c.coefficientNorm ℓ x ∘ pr` satisfies the defining equation on
  representatives, so it is in `L²(μ)`. By `memLp_map_measure_iff`,
  `c.coefficientNorm ℓ x` is then in `L²(ν)`.
* `integrable_integral_of_map`: let `F` on `G/A` and `F'` on `G/Z(G)` agree on
  representatives with the same function on `G`. Then `F = F' ∘ pr`. So
  integrability of `F'` for `ν`, and the value `∫ F' dν`, carry over to `F` and
  `μ` (`integrable_map_measure`, `integral_map`).
* `memLp_two_iff_of_mul_right_invariant`: Part A applied to `f²`
  (`memLp_two_iff_integrable_sq`), in both directions.

The five conjuncts:

1. **Convergence.** `FZ` equals `c.coefficientNorm ℓ x` and `FA` equals
   `FZ ∘ pr`, both by comparing on representatives. `MemLp FA 2 μ` is
   equivalent to `MemLp FZ 2 ν` (`memLp_map_measure_iff`). `MemLp FZ 2 ν` is
   equivalent to `MemLp FZ 2 μZ` by `memLp_two_iff_of_mul_right_invariant`.
   That lemma applies because `FZ` is continuous
   (`continuous_coefficientNorm`) and right invariant under a compact open
   subgroup of `G/Z(G)`.
2. **IV.3.2 Proposition.** Apply `essentiallySquareIntegrableAdmissible G ν`
   to the twist witness converted by `exists_memLp_map_of_squareIntegrable`.
3. **IV.3.2 Lemma.** Apply `squareIntegrableUnitarySemisimple G ν` to
   `⟨admissibility, c, L²(ν) bounds⟩`.
4. **IV.3.3 Lemma.**
   (i) `schurOrthogonality G ν` gives the formal degree `d > 0`. For the given
   `F` on `G/A`, the comparison function `F'` is
   `orthogonalityIntegrand (Z(G)) c.acts c.acts x₁ ℓ₁ₜ x₂ ℓ₂ₜ` on `G/Z(G)`,
   built from the twisted functionals
   `ℓᵢₜ = (smoothContragredientTwistEquiv ω π hω).symm ℓᵢ`. The factors `ω(g)`
   and `ω(g⁻¹)` cancel, so `F'` takes the required values on representatives.
   `integrable_integral_of_map` then moves integrability and
   `∫ F dμ = ℓ₁(x₂) ℓ₂(x₁) / d` back to `G/A`.
   (ii) The common character `χ` gives
   `F' = orthogonalityIntegrand (Z(G)) h₁ h₂ x₁ ℓ₁ x₂ ℓ₂`. The vanishing
   relation of `schurOrthogonality G ν` moves to `G/A` in the same way.
5. **IV.3.3 Corollary.** `coefficients_linearIndependent_of_irreducible` gives
   linear independence directly from irreducibility, pairwise
   non-isomorphism and nonzero vectors and functionals. No integrability is
   needed.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
