# Compactness of the cuspidal convolutions for adelic GL_n

`Langlands.Automorphic.GroupSchemeFunctions.generalLinearFullAEL2CuspidalCompactness`
proves `GeneralLinearFullAEL2CuspidalCompactnessStatement`. The proof
covers every number field `F`, every rank `n`, the supplied
positive-central quotient data, and every `f : C_c(AdelicGroupPoints F G, ℂ)`
with its integrability witness, where
`G = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
The operator is the original
`fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc Measure.haar f hf`
on `S = fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc`, with the full
group's Haar measure. The hypotheses `hPD` and `hG` are used only through
the cusp space and the cuspidality comparisons named below.

## Reduction to the ambient operator

Let `R = haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f hf`
on `Lp ℂ 2 μQ`, with `μQ = positiveRationalQuotientHaarMeasure F G T i`,
and let `V = R ∘L S.subtypeL`. By `fullAEL2CuspidalIntegratedAction_val`
the value of the cusp-space operator at `v` is `V v`. In particular
`V v ∈ S`, so the cusp-space operator equals
`S.orthogonalProjectionOnto ∘L V`. It therefore suffices to prove that
`V` is compact (`IsCompactOperator.clm_comp`).

## Rank zero

For `n = 0` the matrices over `Fin 0` form a single point, so the adelic
group and the quotient `Q = PositiveRationalQuotient F G T i` are
subsingletons and `Q` is compact. The indicator of `Q` itself acts as the
identity on `L²`. By `isCompactOperator_positiveQuotientL2CompactPart`
with the compact set `Q`, the operator `R` is compact, hence so is `V`.

## Positive rank

The compact operators are closed in operator norm
(`isClosed_setOfPred_isCompactOperator`), so it suffices to approximate
`V` within any `δ > 0` by a compact operator.

1. `exists_positiveQuotientL2ConvolutionOscillation` gives a constant
   `C ≥ 0`. Put `ε = δ / (C + 1)` and take the neighborhood `U` of `1` that
   it gives for `ε`.
2. `exists_compact_cuspDisplacementCover` for `U` gives a compact `D ⊆ Q`.
   Let `W = quotientL2Indicator D ∘L V`. It is compact by
   `isCompactOperator_positiveQuotientL2CompactPart`.
3. Let `v ∈ S`. The oscillation theorem gives a continuous `ψ` equal to
   `V v` almost everywhere, and a class `B` with `‖B‖ ≤ C · ‖v‖`, such
   that `‖ψ q - ψ (q · a)‖ ≤ ε · ‖B q‖` for almost every `q` and all
   `a ∈ U`. Since `V v ∈ S`, `groupSchemeFullAEL2ContinuousCuspidality`
   shows that the pullback of `ψ` lies in
   `normalizedParabolicCuspidalSubrepresentation F G hPD hG`.
4. On `D` the class `(V - W) v` vanishes almost everywhere, by
   `quotientL2Indicator_ae`. Off `D` it equals `ψ`. The displacement
   cover, applied with `M = ε · ‖B q‖`, gives `‖ψ q‖ ≤ ε · ‖B q‖` for
   almost every such `q`. Hence
   `‖(V - W) v‖ ≤ ε · ‖B‖ ≤ ε · C · ‖v‖`, by
   `Lp.norm_le_mul_norm_of_ae_le_mul`.
5. Therefore `‖V - W‖ ≤ ε · C < δ`.

The case `n = 1` falls under the positive-rank argument. There are no
proper blocks, so the cusp cover places every point in its compact part.

## Route and sources

The statement's Markdown follows Getz–Hahn, *An Introduction to
Automorphic Representations* (2024). There Proposition 9.4.7 (printed
pp. 257–259) proves rapid decay of `R(f)φ` on Siegel sets for smooth `f`
and cuspidal `φ`. Lemma 9.3.3 (pp. 247–248) turns the resulting uniform
evaluation bound into a Hilbert–Schmidt kernel, and Corollary 9.3.2 notes
that Hilbert–Schmidt operators are compact. The implemented proof does not
use the Fourier expansion, the rapid-decay estimate or smooth approximation
of `f`. It works directly with the continuous weight. The Hilbert–Schmidt
criterion is applied only to the truncation to a compact set, and
cuspidality enters through the cusp cover and the vanishing of block
constant terms. Together these make the truncation error arbitrarily
small in operator norm.
