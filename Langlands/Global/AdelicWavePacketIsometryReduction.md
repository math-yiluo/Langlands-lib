# The wave packet isometry from Proposition 2 of Lapid

Module `Langlands.Global.AdelicWavePacketIsometryReduction` proves the
implication

```
Langlands.Global.wavePacketIsometry_of_innerProduct
    (h2 : WavePacketInnerProductStatement)
    (hI : InducedInnerProductIntegrableStatement) :
    WavePacketIsometryStatement
```

It reduces the wave packet isometry (Lapid 2011, Theorem 2; Arthur 2005,
Theorem 7.2 (b)) to two other results:

- Lapid's Proposition 2, the published statement
  `Langlands.Global.WavePacketInnerProductStatement`;
- the absolute convergence of the inner products `(·,·)_P` on `A^2_P`,
  `Langlands.Global.InducedInnerProductIntegrableStatement` (module
  `Langlands.Global.AdelicInducedInnerProductIntegrableStatement`).

The two statements are hypotheses of the theorem and are not asserted.
Neither has been proved yet, so this module does not prove
`WavePacketIsometryStatement` unconditionally. Once both are proved, the
isometry is `wavePacketIsometry_of_innerProduct` applied to the two proofs.
The theorem uses only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

The module also proves some general lemmas in the namespace
`Langlands.Global.AdelicGroupPoints`, described below.

## Sources and provenance

- E. Lapid (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, §3, printed
  p.314 (volume PDF page 323). This page has Proposition 2, formula (4), the
  space `L` with the norm `∑_P |P(M_P)|⁻¹ ‖F_P‖²_*` and the symmetry
  condition `F_{P'}(wλ) = M(w, λ)F_P(λ)`, and Theorem 2. Lapid writes "We
  conclude" Theorem 2 from Proposition 2 and gives no further argument.
- J. Arthur, *An introduction to the trace formula* (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2 (b),
  printed p.35 (PDF page 47), with the weights
  `n_P = ∑_{P'} |W(𝔞_P, 𝔞_{P'})|`.
- J. Getz and H. Hahn (2024), registered as
  `getz-hahn-2024-automorphic-representations`, §10.5, (10.22)–(10.24).

The proof follows the guide in the task contract. It expands `‖Φ‖²`, applies
Proposition 2 to every ordered pair of members, and uses the symmetry
condition, the measure-preserving coordinate changes and the counting
identity `∑ i, (n_P i)⁻¹ |Ω(P i, P i')| = 1` of
`Langlands.Global.AdelicWeylSetAssociation`. The intermediate lemmas are
internal.

## General lemmas

### Sesquilinearity of `inducedInnerProduct`

- `inducedInnerProductIntegrand K p l e β φ ψ` is the function
  `(k, x) ↦ β(y(m)) m^{-2ρ_P} φ(m k) conj ψ(m k)` on `K × M(F) \ M(𝔸)`,
  with `m = x.out`. This is the integrand of `inducedInnerProduct`.
  `inducedInnerProductMeasure K hKc μM` is the product of
  `compactHaarProbability` and `discreteQuotientMeasure`. These two
  definitions only name the integrand and the measure.
- `sFinite_discreteQuotientMeasure_of_haar`: the quotient measure is s-finite. It is
  the image of a restriction of the Haar measure `μM`.
- `inducedInnerProduct_eq_integral`: if the integrand is integrable for the
  product measure, then `inducedInnerProduct` (an iterated integral) equals
  its integral over the product (`integral_prod`, Fubini).
- `inducedInnerProductIntegrand_sum_sum` and `inducedInnerProduct_sum_sum`.
  Suppose every integrand `(φ x, ψ y)` is integrable. Then
  `(∑ x, a x φ x, ∑ y, b y ψ y)_P = ∑ x, ∑ y, a x · conj (b y) · (φ x, ψ y)_P`.
  The integrands agree pointwise. The integral of the finite sum is computed
  over the product, where it is linear.

### Coordinates

- `le_of_measurePreserving_linearMap`: if a linear map `ℝᵃ → ℝᵇ` preserves
  Lebesgue measure, then `b ≤ a`. Otherwise its range is a proper subspace,
  which has measure zero (`Measure.addHaar_submodule`), but its preimage is
  all of `ℝᵃ`, which has positive measure.
- `integral_comp_spectralMeasure`: for `a = b`, a measure-preserving
  `f : ℝᵃ → ℝᵇ` and continuous `g`,
  `∫ g ∘ f d(spectralMeasure a) = ∫ g d(spectralMeasure b)`. Recall
  `spectralMeasure n = (2π)^{-n} · volume`. The scalars agree when `a = b`,
  and `integral_map` handles the change of variables.
- `integrable_comp_spectralMeasure`: if `g` is Lebesgue integrable, then
  `g ∘ f` is integrable for `spectralMeasure a`.

## The proof of `wavePacketIsometry_of_innerProduct`

Fix the data of `WavePacketIsometryStatement`. Write `F i x = ∑ j, c i j x · v i j`
and `x'_t = (e i')⁻¹ (realWeylParameter (l i) (cw i i' t) (π i') (e i x))`
for `t : T i i'`.

1. Proposition 2 for each pair. `h2` is applied to `P = P i`, `P' = P i'`.
   The other arguments are the data of members `i` and `i'`, the measure
   `μM i'`, the weight `β i'`, the enumeration `T i i'` and the expansions
   `ψ i i'`, `coeff i i'`. It gives `Θ i, Θ i' ∈ L²(μG)` and formula (4),
   with its right side expanded as in the statement. The coordinates on both
   sides are `e i` and `e i'`.
2. Integrability. `hI`, applied to the data of member `i`, shows that the
   integrand of `(φ, φ')_{P i}` is integrable for all `φ, φ' ∈ A^2_{P i}`.
   This is used for the vectors `v i j` and `ψ i i' t j q`, which lie in
   `A^2_{P i}` and `A^2_{P i'}` by hypothesis.
3. The norms `N i x = (F i x, F i x)_{P i}`. By sesquilinearity,
   `N i x = ∑ j, ∑ j', c i j x · conj (c i j' x) · (v i j, v i j')_{P i}`.
   So `N i` is continuous with compact support, because the `c i j` are
   smooth with compact support. Hence it is integrable for Lebesgue measure
   and for `spectralMeasure (n i)`.
4. Equal ranks. Let `t : T i i'`. By `IsWeylConjugation.exists_symm` and the
   surjectivity of the enumeration, some `t' : T i' i` exists. The two
   coordinate changes `x ↦ x'_t` and back are linear and preserve Lebesgue
   measure, so `le_of_measurePreserving_linearMap` gives `n i = n i'`.
5. The integrand of (4). The Weyl compatibility rewrites `F i' (x'_t)` as
   `∑_{(j, q)} (c i j x · coeff i i' t j q (i e i x)) · ψ i i' t j q`.
   Sesquilinearity in the first argument then shows that the `t`-th summand
   of the integrand in Proposition 2 is `N i' (x'_t)`.
6. The pair `(i, i')`. By steps 1 and 5,
   `(Θ i, Θ i') = ∫ ∑ t, N i' (x'_t) dx = ∑ t, ∫ N i' (x'_t) dx`.
   Each term equals `∫ N i' d(spectralMeasure (n i'))` by step 4 and
   `integral_comp_spectralMeasure`. So
   `(Θ i, Θ i') = |T i i'| · ∫ N i' d(spectralMeasure (n i'))`.
7. Expanding `‖Φ‖²`. `Φ = ∑ i, (n_P i)⁻¹ Θ i` is in `L²` as a finite sum
   (`memLp_finsetSum`). This is the first conclusion. Each product
   `Θ i · conj Θ i'` is integrable (Hölder for `2, 2`), so
   `∫ Φ conj Φ = ∑ i, ∑ i', (n_P i)⁻¹ (n_P i')⁻¹ (Θ i, Θ i')`.
8. Counting. `(n_P i')⁻¹ · ∑ i, (n_P i)⁻¹ |T i i'| = (n_P i')⁻¹`. If
   `n_P i' = 0`, both sides are `0`. Otherwise the identity follows from
   `sum_inv_card_mul_card_eq_one` of `AdelicWeylSetAssociation`, cast from
   `ℝ` to `ℂ`.
9. Conclusion. `‖Φ‖² = Re (Φ conj Φ)` pointwise, and `integral_re` moves
   `Re` outside the integral. Steps 6–8 give
   `∫ ‖Φ‖² = Re ∑ i', (n_P i')⁻¹ ∫ N i' = ∑ i', (n_P i')⁻¹ Re ∫ N i'`.
   Finally `Re ∫ N i' = ∫ Re N i'` (`integral_re`, using step 3), which is
   the right side of the statement.

## Notes

- The unweighted terms. If `n_P i' = 0`, then `T i' i''` is empty for every
  `i''`, and in particular `T i' i'` is empty. The statement then weights
  `Θ i'` by `(n_P i')⁻¹ = 0`, and step 8 also covers this case.
- Hypotheses not used. The proof does not use `∫ β i = 1`, the meromorphy
  data `E i j`, `D i`, `DM i`, or the expansion identities directly. They are
  passed to Proposition 2 unchanged. The retractions `l i ≫ π i = 𝟙` are
  used in the counting and in Proposition 2.
- The integrability hypothesis. Step 2 is the only use of `hI`. Without it,
  the expansions in steps 3 and 5 would not hold, since `inducedInnerProduct`
  is defined through Bochner integrals, which are `0` for non-integrable
  functions.

The pointwise integrand is defined alongside the [induced inner product](AdelicInducedInnerProduct.md).
