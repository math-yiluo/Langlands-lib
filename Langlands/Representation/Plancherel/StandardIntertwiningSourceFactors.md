# Source Haar measures on the actual intertwining factors

This internal construction implements the common compact-open scale of
Waldspurger (2003), I.1, printed p.240 / PDF page 6, zero-based index 5,
on the actual carriers used by the existing standard-intertwining
factorization. The source fixes a special maximal compact subgroup and
normalizes every closed algebraic subgroup by giving its intersection
with that compact subgroup mass one. Here one compact open `Q` is supplied.
Existence of the source special compact and reductive realization of the
supplied ordered charts remain separate obligations.

The setting is a topological group `G`, closed original subgroups
`U₀`, `U₁`, `U₂`, `V`, `W` as used by each declaration, and supplied
`OrderedSubgroupFactorization` data `D`. Each measure carrier has its
displayed Borel measurable structure. `intersectionAmbientHom A B`
forgets the two subtype wrappers of `A.subgroupOf B`; its closed embedding
is proved by composing the closed subtype embeddings. `sourceIntersectionHaar`
uses `compactOpenHaarAlong` for this actual map into `G`. It is regular
Haar and assigns mass one to the elements whose original ambient value
lies in `Q`.

`sourceNestedKernelHaar`, `sourceNestedComplementHaar` and
`sourceSecondComplementHaar` are intrinsic Haar measures on, respectively,

- `(U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)`;
- `(V.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)`;
- `W.subgroupOf U₂`.

Their embedding maps use the existing continuous group equivalences to
the endpoint intersection, `V` and `W`, followed by the original ambient
inclusions. These are exactly the underlying ambient-element maps; the
equivalences only change subtype wrappers. Their closed embedding proofs
use the actual equivalences and closedness of the corresponding original
subgroups. These measures are never restrictions of ambient Haar.

`sourceMiddleCompactOpen`, `sourceTargetCompactOpen` and the two
complement compact opens are inverse images of the same `Q` under these
literal ambient maps. `intersectionFactorScalar_source` and
`secondFactorScalar_source` substitute the three actual mass-one
equalities into each existing correction scalar, proving that both
scalars are one. They need neither local compactness nor a quotient
measure or product geometry hypothesis.

Under local compactness of `G`, `intersectionKernelMeasure_source`
identifies the transported nested kernel with `sourceIntersectionHaar`
on `U₀.subgroupOf U₂`. `intersectionNormalizedFactor_source` and
`secondNormalizedFactor_source` identify the two explicitly normalized,
transported factor measures with `subgroupCompactOpenHaar Q` on `V`
and `W`. The proof first removes the scalar correction, then applies
`measurePreserving_compactOpenHaarAlong` to the actual equivalence and
its unchanged ambient-element map. That theorem uses regular Haar
uniqueness and the shared mass-one set, so no scalar remains.

No quotient measure is selected, replaced or rescaled in this unit.
Right invariance, compatible Weil measures for the actual source scale,
the local compact-open product geometries, reductive chart realization,
convergence, integral representability and rational continuation remain
application obligations. This unit does not assert a standard-integral
composition theorem or close a whole-task Plancherel condition.
