# Krull continuity of automorphism conjugation: M001.001 target

`Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongrStatement`
is the proposition that, for an algebra equivalence `e : E ≃ₐ[F] E'`, the map
`AlgEquiv.autCongr e : (E ≃ₐ[F] E) ≃* (E' ≃ₐ[F] E')` is continuous.
On an automorphism `σ`, this map sends `x : E'` to `e (σ (e.symm x))`.
Both automorphism groups carry Mathlib's canonical `krullTopology` instances.
Their identity neighborhoods contain the fixing subgroup of a
finite-dimensional intermediate field.

The field carriers `F`, `E` and `E'` are implicit and have independent
universes, as in the source's `{F E E' : Type*}` binder. The three `Field`
instances and the two `Algebra` instances occur in source order, followed by
the explicit argument `e`. There is no algebraicity, separability, normality,
finite-dimensionality or characteristic assumption on the extensions.

## Source and exact adaptation

The original is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean`,
lines 28–57: `AlgebraicNumberTheory.continuous_algEquiv_autCongr`.
Its signature is at lines 28–33; its proof is at lines 33–57.
The inventory and task locator give lines 28–54, but that range stops inside
the proof; the complete original theorem was read through line 57.
The full file and its section context were read. Its SHA-256 is
`40b9e61892ae3b770967cee9c5d95bd41c2d0357909af82ab0e38a8a527be77f`.
The readable original is
[SeparableClosureEmbedding.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean>).

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No project `notes/errata` directory was present at preparation; this records
only the local lookup.

| Source | Adaptation |
| --- | --- |
| `AlgebraicNumberTheory.continuous_algEquiv_autCongr` | `Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongrStatement` |
| Theorem signature at lines 28–33 | A `def` returning `Prop`, with the same binders and body `Continuous (AlgEquiv.autCongr e)` |
| Proof at lines 33–57 | Omitted; this unit supplies the target for a separate proof |
| `Mathlib.FieldTheory.KrullTopology` | Retained as the sole import |
| `Mathlib.FieldTheory.IsSepClosed` and `Mathlib.NumberTheory.NumberField.Basic` | Omitted; used by later source declarations |
| `noncomputable section` and unused `universe u v` | Omitted; the target uses the source's independent `Type*` universes |
| Later declarations from line 59 onward | Omitted |

The namespace, extraction and import changes are recorded in the Lean header.
No proof, compatibility patch, shared draft or feasibility implementation is
reused. Worker 168 wrote this extraction directly from the pinned original.

## Reuse and dependencies

The module reuses Mathlib's `AlgEquiv.autCongr`, its automorphism group
structures, `Continuous` and `krullTopology`; it introduces no new instances.
The single retained import provides these definitions without any NYLL
prerequisite.

The related published theorem
`Langlands.LocalGalois.semilinearAutCongr_continuous` in
`Langlands/Galois/Local/AbsoluteProof.lean` concerns compatible semilinear
field equivalences but assumes `Algebra.IsAlgebraic K L`. Its signature and
proof were inspected: it uses open stabilizers of individual elements via
`stabilizer_isOpen_of_isIntegral`. It therefore does not supply this target
for arbitrary extensions. Mathlib's `AlgEquiv.autCongr` is the exact algebraic
conjugation map, while its `galGroupBasis` conjugation law concerns inner
conjugation within a single automorphism group. These related results do not
identify an already published theorem of the full source generality.

This module states the continuity proposition only. A future proof must prove
this exact target separately. The source proves continuity at the identity
by transporting a finite-dimensional intermediate field through `e.symm`;
that route is recorded here as source context, not as an implemented proof.

## Development validation

The target was compiled and its full declaration inspected by the Lean
service in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
Inspection reports three universe parameters and
`statement_returns_prop: true`, with no errors or warnings.
This development check supplies no proof or independent acceptance.

## Attribution

The original copyright, license and author header is preserved. The existing
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and full
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged. Their
SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
matching the pinned originals. The unit is the source theorem M001.001 in the
published NYLL declaration partition. It provides no host reciprocity,
class-formation or cohomological comparison result.
