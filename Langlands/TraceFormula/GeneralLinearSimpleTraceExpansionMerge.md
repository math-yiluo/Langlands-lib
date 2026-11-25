# The simple trace formula for `GL_n` on a finite sum of functions with their own expansions

Module `Langlands.TraceFormula.GeneralLinearSimpleTraceExpansionMerge`, namespace
`Langlands.TraceFormula`. Notation as on the page of `GeneralLinearSimpleTraceFormulaStatement`
(the module repeats its two local instances and the local notation `GLₙ`).

`GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h` (`GeneralLinearTensorSimpleTraceFormulaStatement`)
is the conclusion of the simple trace formula for one function `f`, with its own family of
representatives. This module shows that a finite sum of continuous compactly supported functions,
each satisfying it, satisfies it too, with one family, provided the traces add.

## Statements

- `integrable_comp_positivePointMap_mul F G T i hi I e hc hg hgc z`: for a group scheme `G` over `F`
  (affine, locally of finite type), `g : AdelicGroupPoints F G → ℂ` continuous (`hg`) with compact
  support (`hgc`) and `z : normOneSubgroup F G`,

  `Integrable (fun a => g (positivePointMap F G T i a * (z : AdelicGroupPoints F G)))
    (normalizedPositiveHaarMeasure F G T i hi I e hc)`.

  So the average `f¹(z) = ∫ f(a z) da` over the positive points `A⁺` of the central torus is
  additive on such functions, at every point `z`.

- `generalLinearSimpleTraceExpansion_finsetSum F n T i hi I e hc v h g hgc hgs hg hfg hexp htc htr`:
  for `f` with `h : Integrable f Measure.haar`, `g : Fin N → AdelicGroupPoints F GLₙ → ℂ` with every
  `g k` continuous (`hgc`), with compact support (`hgs`) and integrable (`hg`),
  `hfg : ∀ x, f x = ∑ k, g k x`,
  `hexp : ∀ k, GeneralLinearSimpleTraceExpansion F n T i hi I e hc v (g k) (hg k)`,
  `htc : IsTraceClass (haarQuotientL2IntegratedAction F GLₙ T i hi I e hc Measure.haar f h)` and
  `htr : operatorTrace (R f) = ∑ k, operatorTrace (R (g k))` (with `R` that operator),

  `GeneralLinearSimpleTraceExpansion F n T i hi I e hc v f h`.

## Proofs

`normOneDecomposition` is a homeomorphism `D : A⁺ × G(𝔸_F)¹ ≃ G(𝔸_F)`, `(a, z) ↦ a z`. The function
`a ↦ g(D(a, z))` is continuous; it vanishes outside the closed set `{a | D(a, z) ∈ supp g}`, which
lies in the compact set `pr₁(D⁻¹(supp g))`. A continuous function with compact support is integrable
for the Haar measure `normalizedPositiveHaarMeasure` (`normalizedPositiveHaarMeasure_isHaarMeasure`).

For the sum: the averages satisfy `f¹(z) = ∑ k, g_k¹(z)` for every `z` (`integral_finsetSum` and the
first statement). The second component of each `hexp k` is, by definition, the data of
`exists_simpleTraceGeometricExpansion_sum` for `G(𝔸_F)¹`, `Γ = rationalNormOneSubgroup F GLₙ`,
`μG = Measure.haar`, `φ k = g_k¹`, `t k = tr R(g k)` and `P` regular ellipticity at `v` of the image in
`GL_n(F_v)`; that theorem gives one family for `∑ k, g_k¹ = f¹` and `∑ k, tr R(g k) = tr R(f)`.
Together with `htc` this is `GeneralLinearSimpleTraceExpansion` for `f`.

## Declarations, in order

- `integrable_comp_positivePointMap_mul`
- local instances `generalLinearExpansionMergeIsAffine`, `generalLinearExpansionMergeSmooth` and the
  local notation `GLₙ`
- `generalLinearSimpleTraceExpansion_finsetSum`

## Literature

Getz–Hahn, *An introduction to automorphic representations* (2024), §18.4, Corollary 18.4.1 and the
paragraph after it (printed p. 485): the simple trace formula with its geometric side indexed by
conjugacy classes; the additivity of both sides in the test function is implicit there.
