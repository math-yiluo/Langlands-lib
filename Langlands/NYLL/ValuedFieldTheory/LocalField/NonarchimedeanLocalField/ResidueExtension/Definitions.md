# Integer-ring map of a valuation extension

The module defines
`Langlands.NYLL.LocalFieldTheory.integerRingMapOfValuationExtension` and its
`integerRingMapOfValuationExtension_isLocalHom` instance. They are the exact
namespaced adaptations of NYLL M138.001–002.

## Pinned source correspondence

Naganori Yamaguchi,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L34-L48),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file SHA-256
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Source lines 1–100 and 333–343 were read for this extraction.

| Unit | Original name in `LocalFieldTheory` | Source lines | Adapted name in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- | --- | --- |
| M138.001 | `integerRingMapOfValuationExtension` | docstring 34–35, definition 36–40 | `integerRingMapOfValuationExtension` |
| M138.002 | `integerRingMapOfValuationExtension_isLocalHom` | docstring 42, instance 43–48 | `integerRingMapOfValuationExtension_isLocalHom` |

The registered sources are `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The public partition is
`notes/reuse/nyll-public-port/m121-m144.md`, section M138.

## Parameters and construction

Both declarations retain exactly one universe `u`, explicit
`(K L : Type u)`, then instance binders in this order:
`[Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]`
and
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
No topology, local-field, finite-dimensionality or nontriviality assumption is
added. The two carriers remain in the same universe as in the source.

The scoped notation `𝒪[K]` denotes the actual
`Valuation.integer (ValuativeRel.valuation K)` subring of `K`, and likewise
for `L`. Mathlib's `Valuation.HasExtension.instAlgebraInteger` equips these
rings with the restriction of the supplied `algebraMap K L`. The definition
body is unchanged: `algebraMap 𝒪[K] 𝒪[L]`, with type `𝒪[K] →+* 𝒪[L]`.
No supplied object is replaced or newly chosen.

The source instance is retained with its original global scope and default
priority. Its proof is unchanged: it changes the goal to
`IsLocalHom (algebraMap 𝒪[K] 𝒪[L])` and calls `infer_instance`.
Mathlib's existing
`Valuation.HasExtension.instIsLocalHomValuationInteger` supplies this fact.
Thus this instance is the source's named wrapper for the canonical instance;
it introduces no different algebra, local-ring structure or conflicting
mathematical choice. `IsLocalHom` is a proposition.

## Modifications and imports

Worker 252 made these changes on 13 November 2026:

- prefixed `LocalFieldTheory` with `Langlands.NYLL`;
- extracted only M138.001–002 and replaced the source module documentation
  with documentation of those two declarations;
- replaced the source's broad Mathlib imports and NYLL `ResidueUnits` import
  with `Mathlib.RingTheory.Valuation.Extension` and
  `Mathlib.Topology.Algebra.Valued.ValuativeRel`;
- added this correspondence and modification record.

The source docstrings, `noncomputable section`, universe, binder kinds and
order, actual definition body, instance scope and instance proof are
preserved. The omitted source units do not enter this construction. No
additional NYLL declaration, theorem target or theorem proof is included.

## License

The original copyright and author header is retained. NYLL is Apache-2.0;
the Library retains its upstream `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`, with SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development check

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
compiled the module with zero errors and warnings. Inspection of the map
reported a definition with exactly the level parameter `u` and only
`propext`, `Classical.choice` and `Quot.sound`. This author check does not
establish independent acceptance or publication.
