# JPSS L-polynomials and epsilon factors along an isomorphism of topological fields

Author: Worker 5731. This is a supporting lemma module for the proof of
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement` (Task 5230).
It states no new published mathematics. It shows that the published
Rankin–Selberg L-polynomial and epsilon-factor relations of
`Langlands.Representation.RankinSelberg.PairLFactor` and `EpsilonFactor`
(Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions*,
Amer. J. Math. 105 (1983), Theorem 2.7, as formalized there) are invariant under
an isomorphism of topological fields. This is the expected fact that these
relations are defined by transport of structure: nothing in them depends on
more than the topological field.

## Setting

In namespace `Langlands.RankinSelberg.FieldTransport`, fix `σ : F ≃+* E` with
`hσ : Continuous σ`, `hσs : Continuous σ.symm`, and write
`T = fieldEquiv n σ hσ hσs` for the entrywise isomorphism `GL_n(F) ≃ₜ* GL_n(E)`.
Representations `π`, `τ` are representations of general linear groups over `E`
on complex vector spaces, and `π ∘ T` denotes the pullback
`π.comp (fieldEquiv (r + 1) σ hσ hσs).toMonoidHom` to `GL_{r+1}(F)`, the
convention of the published `SupercuspidalRep.fieldPullback`. Characters,
absolute values and scalar Haar measures are related by
`hψ : ∀ x, ψ' (σ x) = ψ x`, `habv : ∀ x, abv' (σ x) = abv x` and
`hν : ν'.measure = ν.measure.map σ`, as in `FieldTransport.Integrals`. A
measure `μ` on the left unipotent quotient over `F` is compared with the
pushforward `μ.map (quotientHomeomorph σ hσ hσs n)` over `E`.

## Whittaker spaces, functionals and models

- `whittakerEquiv σ hσ hσs hψ n` and `inverseWhittakerEquiv σ hσ hσs hψ n` are
  the complex-linear equivalences `W ↦ W ∘ T⁻¹` from the published
  `WhittakerFunctions ψ n` to `WhittakerFunctions ψ' n`, and likewise for
  `InverseWhittakerFunctions`. They are `equivariantEquiv` of
  `FieldTransport.Group`, applied with `standardCharacter_unipotentEquiv`
  (respectively its inverse-character version) of `FieldTransport.Integrals`.
  `whittakerEquiv_apply_fieldEquiv` and `inverseWhittakerEquiv_apply_fieldEquiv`
  state that the image takes the value `W g` at `T g`.
- `glFunctionalEquiv σ hσ hσs hψ n π` identifies the published standard
  Whittaker functionals `glFunctionals ψ n (π ∘ T)` with `glFunctionals ψ' n π`
  (via `functionalTransportEquiv`; the underlying linear functional is the same).
  `glInverseFunctionalEquiv` does the same for `glInverseFunctionals`.
- `glModelEquiv` and `glInverseModelEquiv` are the induced bijections of the
  published coefficient models, `f ↦ f ∘ T⁻¹`, with value lemmas
  `glModelEquiv_apply_fieldEquiv` and `glInverseModelEquiv_apply_fieldEquiv`.
- `whittakerEquiv_mem_whittakerSet_iff`: `whittakerEquiv … f` lies in the
  published `whittakerSet ψ' n π` (the union of the coefficient models of all
  standard functionals) exactly when `f` lies in `whittakerSet ψ n (π ∘ T)`.
  `inverseWhittakerEquiv_mem_inverseWhittakerSet_iff` is the analogue for
  `inverseWhittakerSet`.
- `hasModelMinusOneScalar_glInverseFunctionalEquiv_iff`: the published
  condition `HasModelMinusOneScalar` (that `-1` acts on the model by the scalar
  `ζ`) holds for `τ` and the transported functional exactly when it holds for
  `τ ∘ T` and the original one, because `T (-1) = -1`.

## Zeta values and L-polynomials

- `equalRankValuesOf_map` and `unequalRankValuesOf_map`: the published sets
  `equalRankValuesOf` and `unequalRankValuesOf` of rational functions
  represented by convergent JPSS integrals over given sets of Whittaker
  functions agree, when the `E`-side function sets are the images of the
  `F`-side ones under `whittakerEquiv` and `inverseWhittakerEquiv`. A value over
  `E` comes from functions `W ∘ T⁻¹`, `W' ∘ T⁻¹` and a row function `Φ ∘ σ⁻¹`
  (`rowTestEquiv`), whose integral and convergence are those over `F` by
  `equalRankIntegral_map`, `equalRankConverges_map_iff` and their unequal-rank
  analogues. The rectangular measures are `rectangularMeasure ν'` and
  `rectangularMeasure ν`; both scalar measures are assumed σ-finite.
- `equalRankZetaValues_map` and `unequalRankZetaValuesAt_map`: the published
  zeta-value sets `equalRankZetaValues` of `(π, τ)` over `E` and
  `unequalRankZetaValuesAt j k hr` (for `r = n + (j + k + 1)`) equal those of
  `(π ∘ T, τ ∘ T)` over `F`.
- **`isPairLPolynomial_comp_iff`**: for `π` on `GL_{r+1}(E)`, `τ` on
  `GL_{n+1}(E)` and `P : ℂ[X]`,

  `IsPairLPolynomial q ψ' abv' (μ.map (quotientHomeomorph σ hσ hσs n)) ν' π τ P ↔
   IsPairLPolynomial q ψ abv μ ν (π ∘ T) (τ ∘ T) P`.

  The proof splits on `n < r`, `n = r`, `r < n` with the published
  `isPairLPolynomial_of_lt`, `isPairLPolynomial_self` and
  `not_isPairLPolynomial_of_lt`; in the first two cases the normalized
  generators are of equal sets of zeta values.

## Epsilon equations

Now `F` and `E` are topological rings.

- `equalRankModelIntegral_map` and `dualEqualRankModelIntegral_map`: the
  published equal-rank model integral and its dual (built from the transformed
  functions `firstDualFunction`, `secondDualFunction`) of transported model
  functions over `E` equal those over `F`. `equalRankRationalValues_map` and
  `dualEqualRankRationalValues_map` deduce equality of the published rational
  value sets for fixed functionals.
- `equalRankEpsilonEquation_map_iff`: the published fixed-monomial equal-rank
  functional equation `EqualRankEpsilonEquation q ψ' abv' (μ.map …) ν' π τ ℓ₂ ℓ₂' c m`,
  for the transported functionals, holds exactly when
  `EqualRankEpsilonEquation q ψ abv μ ν (π ∘ T) (τ ∘ T) ℓ ℓ' c m` holds. The
  existential data `ζ`, `P`, `Pdual` are unchanged; the Fourier partner of a
  transported row function is the transported Fourier partner
  (`isRowFourierPair_map_iff`); the rational continuations `R`, `Rdual` are
  unchanged because the integrals are equal.
- `unequalRankIntegralAt_model_map`, `dualUnequalRankModelIntegralAt_map`,
  `unequalRankValuesAt_map`, `dualUnequalRankRationalValuesAt_map` and
  `unequalRankEpsilonEquation_map_iff` are the unequal-rank analogues for
  `n < r`, for the published `UnequalRankEpsilonEquation`. The dual integral
  uses that `T` fixes `blockWeylAt n r hnr` and commutes with right
  translation (`translateWhittaker_fieldEquiv`).

## Epsilon factors

Now `F` and `E` are nonarchimedean local fields (`ValuativeRel`,
`IsNonarchimedeanLocalField`) with Borel measurable structures on `GL_{n+1}`,
its upper unipotent subgroup and the quotient. Two further hypotheses relate the
published normalized Haar measures `generalLinearHaar` and `unipotentHaar` of
`Langlands.Representation.RankinSelberg.Measures`:

- `hG : generalLinearHaar E n = (generalLinearHaar F n).map (fieldEquiv (n + 1) σ hσ hσs)`,
- `hU : unipotentHaar E n = (unipotentHaar F n).map (unipotentEquiv σ hσ hσs (n + 1))`.

For p-adic fields these are proved in `FieldTransport.Padic`.

- `isMulRightInvariant_unipotentHaar_iff`: right invariance of `unipotentHaar`
  holds over `E` exactly when it holds over `F` (by `hU` and
  `isMulRightInvariant_map_iff`).
- `isCompatible_unipotentHaar_map_iff` and
  `compatibleMeasureExists_unipotentHaar_iff`: the published compatibility of a
  quotient measure with `generalLinearHaar` and `unipotentHaar` holds for
  `μ.map (quotientHomeomorph σ hσ hσs n)` over `E` exactly when it holds for `μ`
  over `F`, and existence of a compatible measure transfers
  (`isCompatible_map_iff`, `compatibleMeasureExists_iff`).
- `isEqualRankEpsilonFactor_comp_iff` and `isUnequalRankEpsilonFactor_comp_iff`:
  the published relations `IsEqualRankEpsilonFactor` and
  `IsUnequalRankEpsilonFactor` hold for `(π, τ)` over `E` exactly when they hold
  for `(π ∘ T, τ ∘ T)` over `F`. Each of the four clauses of the definition is
  transported: the measure clause by the previous items; nonzero functionals
  by `glFunctionalEquiv` (which keeps the underlying functional); and the
  universally quantified equation by the equation lemmas above, where every
  compatible quotient measure over `E` is a pushforward `μ.map …` of a measure
  over `F` (`exists_map_eq`).
- **`isPairEpsilonFactor_comp_iff`**: under `hψ`, `habv`, `hν`, `hG`, `hU` (and
  σ-finiteness of `ν'.measure`), for `π` on `GL_{r+1}(E)`, `τ` on `GL_{n+1}(E)`
  and `e : ℂˣ × ℤ`,

  `IsPairEpsilonFactor q ψ' abv' ν' π τ e ↔
   IsPairEpsilonFactor q ψ abv ν (π ∘ T) (τ ∘ T) e`.

  The proof splits on `n < r`, `n = r`, `r < n` with the published
  `isPairEpsilonFactor_of_lt`, `isPairEpsilonFactor_self` and
  `not_isPairEpsilonFactor_of_lt`.
