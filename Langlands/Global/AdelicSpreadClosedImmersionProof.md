# Closed embeddings on actual generic-fiber adelic points

The theorem `Langlands.Global.adelicSpreadClosedImmersion` proves exactly
`Langlands.Global.AdelicSpreadClosedImmersionStatement.{u}`. Its two components
are `curvePlaceSpreadClosedImmersion` and `numberFieldSpreadClosedImmersion`.
The map is literal postcomposition by the given closed immersion on actual
full-adele-valued relative scheme points. Source and target carry the
independently specified arithmetic spread topologies in the target statement.

The proof is by Worker 208, reusing Worker 105's scheme-limit morphism and
closed-immersion descent proofs. The imported target and prerequisite
constructions are unchanged.

## Source and scope

The source-backed conclusion is Conrad, *Weil and Grothendieck approaches to
adelic points*, December 31, 2011, printed p.9, Section 4, opening discussion:
closed immersions give closed embeddings before the additional separatedness
assumption used for later conclusions. Model-morphism and property descent
come from Theorem 3.4(1)–(3), printed pp.5–6; the actual generic-fiber
identification is (3.5.1), printed p.6. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

As explained in the target Markdown, the curve clause is a derived extension
to arbitrary perfect constant fields and the specified compatible
rational-function-field scalar action. It does not assume separability,
finite constants, or a nonempty initial set. The number-field clause retains
every infinite factor. Both clauses retain arbitrary nonaffine and
nonseparated finite-type models, independent initial finite sets and
independent generic-fiber isomorphisms, in arbitrary common universe `u`.
The proof does not assume a closed morphism between the supplied models:
it constructs one after enlarging the initial finite set.

## Descending the prescribed generic morphism

The general helper `modelConeLeg` expresses the actual projection from the
limit pullback of a model to a finite-stage pullback. It uses pullback
symmetries to reconcile the order used by the scheme-limit construction with
the order used by `Over.pullback`. Its first projection is the original
model projection; its second is the limiting base projection followed by the
cone leg.

`exists_modelMorphism` conjugates a supplied relative limit morphism into
the existing `LimitHom` type and applies `exists_level_morphism`. Conjugating
the resulting `LevelHom` back produces a genuine morphism of the
finite-stage models. The lemma retains its precise compatibility square with
`modelConeLeg`; it does not merely assert the existence of some isomorphic
generic morphism.

`modelConeLeg_compIso` compares the cone leg with the first projection of
the iterated pullback, using `modelPullbackCompIso`.
`modelConeLeg_naturality` then turns the retained square into an equality
between actual relative morphisms: pulling the descended map back to the
limit and composing with the target comparison isomorphism equals composing
the source comparison isomorphism with the original map. Both pullback
projections are checked. Consequently `modelConeLeg_closed` proves that this
actual generic pullback is a closed immersion, by conjugating the given
closed immersion with these comparison isomorphisms.

Two further helpers keep the pullback identifications explicit.
`pullbackMap_closed_iff` compares the scheme-limit `baseChangeMap` with
`Over.pullback.map` through pullback symmetries; closed immersions are
invariant under these isomorphisms. `pullbackComp_naturality` proves
naturality of the iterated-pullback comparison on a model morphism.

## Finding a closed model at a later arithmetic stage

For a common initial curve set `S`, the spectrum diagram of the actual
outside-`S` integer rings has limit `Spec F`, by the integer-ring colimit
theorem and `spectrumConeIsLimit`. The integer ring at `S` is noetherian.
The finite-type models are therefore locally noetherian, giving the
quasi-separatedness and finite-presentation hypotheses needed for morphism
descent. `curve_exists_modelMorphism` specializes the preceding general
helper to this diagram.

In `curve_spread_closed_sameBase`, conjugate the given field morphism `g`
by the supplied generic-fiber identifications `e` and `f`, obtaining
`e.hom ≫ g ≫ f.inv`. Descend this specific morphism to a stage `T`.
Its actual generic pullback is closed by `modelConeLeg_closed`.

Apply `spectrumClosedImmersionDescent` to the actual arithmetic system
starting at `T`. The descended morphism is locally of finite type,
quasi-compact and quasi-separated: these properties are derived from its
equation over the finite-type locally noetherian models, rather than added
as assumptions. This yields a later stage `U` where its pullback is a
closed immersion. `pullbackMap_closed_iff` supplies the precise
`Over.pullback.map` form used by the arithmetic models.

The models at `U` are nested pullbacks of the original models. Their
generic-fiber comparison isomorphisms are composed with `e` and `f`.
`modelConeLeg_naturality` and `pullbackComp_naturality` show that the
generic pullback of the closed model map intertwines exactly with `g`
under these composed isomorphisms.

## Transferring the topological conclusion

`curve_spread_closed_of_model` applies
`curvePlaceFixedModelAdele_isClosedEmbedding` to a closed model map.
The actual generic-fiber point equivalence is natural for this map.
Together with its generic-fiber compatibility equation, this identifies
the map conjugated by the two spread point homeomorphisms with literal
postcomposition by `g`. Composition of closed embeddings therefore proves
the required assertion for these new spreads.

`curvePlaceSpreadTopologyIndependence` identifies the new spread
topologies with the original ones, completing the common-base case.
For the full curve theorem, first enlarge the two independent initial
sets to their union. The canonical generic-fiber composition
isomorphisms give valid spreads there. Topology independence rewrites
both original topologies to these common-base topologies, to which the
proved result applies.

The number-field section implements each step for the actual number-field
integer-ring diagram and its colimit, using the full number-field point
equivalences and homeomorphisms. In particular,
`number_spread_closed_sameBase` performs morphism descent, eventual
closed-immersion descent, and the compatibility calculation;
`numberFieldSpreadClosedImmersion` handles the two independent initial
sets by their union. The final theorem pairs the two arithmetic proofs.

This contribution proves the specified-spread closed-embedding target.
Existence of spreads and the other conclusions of the whole-paper program
remain separate obligations.

The model-cone projection, morphism-descent and pullback-composition helpers are
shared with the related spread proofs through
[`AdelicSpreadModelMorphisms`](AdelicSpreadModelMorphisms.md). This integration
consolidation preserves their definitions, hypotheses and conclusions.
