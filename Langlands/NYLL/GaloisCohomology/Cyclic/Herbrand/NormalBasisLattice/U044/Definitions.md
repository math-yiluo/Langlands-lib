# NYLL M144 U044: embedded valuation-ring data

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean).
The retained original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`,
SHA-256 `0eee523e8332a4d9fd6101b8e313c86ade7bcdcfed7b8d60f220aba8ea762931`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
also covered by `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable NYLL erratum was found under `notes/errata/`.

## Exact source correspondence

| Unit | Original declaration | Source lines | Adapted declaration |
| --- | --- | --- | --- |
| M144.044 | `CyclicCohomology.integerRingToFieldLinearMap` | 784–791 | `Langlands.NYLL.CyclicCohomology.integerRingToFieldLinearMap` |
| M144.045 | `CyclicCohomology.integerRingFieldSubmodule` | 795–811 | `Langlands.NYLL.CyclicCohomology.integerRingFieldSubmodule` |
| M144.049 | `CyclicCohomology.maximalIdealFieldSubmodule` | 868–886 | `Langlands.NYLL.CyclicCohomology.maximalIdealFieldSubmodule` |

The first object is the actual inclusion of the extension's valuation integer ring
into the extension field, linear over the base valuation integer ring through the
valuation-extension scalar action. Its addition and scalar-linearity fields retain
the original `rfl` proofs.

The second object is the submodule of extension-field elements belonging to its
valuation integer ring. Its zero, addition and scalar-closure proof fields are
unchanged. Scalar closure uses the element of the extension integer ring supplied
by the actual integer-ring map of the valuation extension.

The third object consists exactly of field images of extension-integer-ring
elements in its maximal ideal. Its existential carrier and every proof field are
unchanged, including the explicit coercion equality at zero and the use of the
integer-ring extension map for scalar multiplication. These are data definitions;
no comparison theorem, normal-basis bound or replacement supplied submodule is
introduced.

## Universes, parameters and dependencies

The source uses a single arbitrary universe `u`, with section variables
`(K L : Type u) [Field K] [Field L] [Algebra K L]`, then
`[FiniteDimensional K L] [IsGalois K L]`, `[ValuativeRel K]`,
`[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, `[ValuativeRel L]` and
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
This section context and M144.049's `omit` clause are retained. The data bodies and
their types use neither finite-dimensional Galois nor topological/local-field
structure, so Lean omits those unused section parameters, as it does in the source.
The fields, algebra, valuations and valuation-extension instance remain in source
order, with the original binder kinds. No new instance is declared.

The imported `Langlands.NYLL.LocalFieldTheory.integerRingMapOfValuationExtension`
is the namespaced M138.001 data definition, whose original body is
`algebraMap 𝒪[K] 𝒪[L]` at
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean:36–40`
in the same pinned source. Mathlib provides the valuation-extension algebra and
module structures; the port does not replace them or assume new scalar laws.
The normal-basis Mathlib import supplies the source's unused Galois section
variables only. The explicit local-field Mathlib import supplies the retained
local-field section variables without relying on the dependency module’s imports.

## Modifications and attribution

Worker 231 extracted these three source data declarations on 13 November 2026,
prefixed the namespace with `Langlands.NYLL`, reduced the original imports to the
ones displayed in Lean and omitted unused namespace-opening commands. The data
bodies, proof terms inside their structures, section parameter order, binder kinds
and source documentation are unchanged. Worker 249 compared all three definition
bodies, including their structure proof fields, byte for byte with the pinned source
and checked assignments of the unapplied declarations to their complete source
telescopes. Worker 249 also made the local-field Mathlib import explicit, so the
retained section context does not depend on transitive imports from M138.001. No theorem is ported as a proof here;
the theorem targets belong to the separate statement modules. This support data
discharges no host class-formation, cup, transfer, Tate or reciprocity target.

The original copyright and author header is retained verbatim. Apache-2.0
attribution is retained in the Library's `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
