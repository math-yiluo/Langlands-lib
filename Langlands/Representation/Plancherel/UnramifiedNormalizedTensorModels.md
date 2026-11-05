# Universal normalized tensor models and coefficient maps

Worker 1585. This is a derived construction from
`UnramifiedUniversalTwist`, `UnramifiedNormalizedModels`,
`Induction.Definitions`, and `Jacquet.Localization`, motivated by
Waldspurger 2003 I.5, printed p.245, and IV.1, printed p.277
(`waldspurger-2003-plancherel`). It adds no finiteness assertion from those
passages.

`tensorMap ν T` is precisely `T.toLinearMap.baseChange B`, where
`B = unramifiedRegularFunctions ν`. It intertwines the actual universal
actions: on a pure tensor both compositions give
`(unramifiedEvaluationRegular ν g * b) ⊗ T (σ g v)`, using the original
intertwining identity. `tensorMap_tmul`, `tensorMap_id`, and `tensorMap_comp`
give its formula and functor laws. `tensorEvaluation_map` proves that
evaluation commutes with T, by tensor induction and complex linearity.

`inducedMap` accepts any B-linear Levi intertwiner. It inflates that
intertwiner along the actual projection, applies the common positive
full-parabolic twist, and applies `smoothInducedMap`. Its value formula
is postcomposition. `inducedMap_id` and `inducedMap_comp` follow by
extensionality on actual functions.

`jacquetMap` accepts any B-linear ambient intertwiner. It is the actual
`Localization.map` at character one, with the common inverse Levi
half-character twist. Its formula sends `[v]` to `[T v]`. The identity
and composition proofs use the quotient universal property, by
precomposition with its surjective canonical quotient map.

For the entire family `ν : I → (M →* ℝ≥0ˣ)`,
`universalInducingRepresentation`, `UniversalInduced`, and
`universalInducedRepresentation` explicitly apply these normalized
constructions to `universalUnramifiedRepresentation ν σ` on the actual
carrier `B ⊗[ℂ] V`. `UniversalJacquet` is the character-one relation
quotient of that full induced model, with inverse-half action
`universalJacquetRepresentation`. Both actions are smooth by the full
smooth-function construction and descent to the quotient. The original
coefficient action need not be smooth for these two conclusions. When
smoothness of the inducing tensor itself is needed, the imported
`isSmooth_universalUnramifiedRepresentation` uses the open full common
norm kernel and smooth σ, and its continuous-norm variant supplies that
openness under its stated local group hypotheses.

`universalInducedMap` and `universalJacquetMap` apply the maps above to
`tensorMap`; their identity and composition laws follow immediately from
the displayed component laws. All coefficient carrier universes remain
independent. This module asserts no evaluation fiber isomorphism,
geometric lemma, compact/full comparison, projectivity, admissibility,
or rationality result.
