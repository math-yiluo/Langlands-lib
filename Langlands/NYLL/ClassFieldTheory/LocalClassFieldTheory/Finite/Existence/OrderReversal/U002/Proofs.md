# Norm transport for an embedded finite abelian extension

The paired Lean theorem
`Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eq`
has the exact published proposition
`Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eqStatement`
as its type, without theorem parameters outside that closed proposition.
Its complete telescope is

```lean
∀ (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  (i : L →ₐ[K] SeparableClosure K), ...
```

The conclusion identifies the actual abstract norm subgroup of
`finiteAbelianAbstractExtensionOfEmbedding K L i`, mapped through
`(baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom`,
with `CyclicCohomology.additiveNormSubgroup K L`. The fields are in
universe zero. There are no additional valuation, topology, local-field,
or comparison hypotheses.

## Implemented proof

Let `E = AlgHom.fieldRange i`. The algebra equivalence
`AlgEquiv.ofInjectiveField i` identifies `L` with this actual intermediate
field. Its underlying linear equivalence supplies a local
`FiniteDimensional K E` instance, and `IsGalois.of_algEquiv` supplies the
local Galois instance.

The proof applies `congrArg Subgroup.toAddSubgroup` to the inverse of
`localNormSubgroup_fieldRange_eq K (SeparableClosure K) L i`. This replaces
the ordinary additive norm subgroup of `L/K` with that of `E/K`.
It then applies `map_finiteNormSubgroup_eq_additiveNormSubgroup K
(SeparableClosure K) E`. The abstract extension's norm subgroup unfolds to
the actual finite norm subgroup of the closed fixing subgroup of `E`,
so the imported comparison has exactly the required remaining conclusion.
Only these local finite-dimensional and Galois instances are installed.

The proof imports the target module `OrderReversal.U002.Statements`,
the published M096.013 theorem from
`SeparableUnitsNorm.Embedding.U013.Proofs`, and the published
M096.007 theorem from
`SeparableUnitsNorm.BaseUnits.NormSubgroup.U007.Proofs`, all under
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite`.
The existing target and its imports are unchanged.

## Source and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean#L61-L81).
The docstring occupies lines 61–63, the theorem head and type lines
64–71, and the implemented proof lines 72–81. This is M402.002 in the
published [NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md).
The full source file was read; its SHA-256 is
`173d65750c2a18cc233fcc94d9fde94e88c7a42709cfb9c27e50bae8e971ba06`.
The enclosing source section has no universe or variable declarations.

| Source declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eq` | `Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eq` |
| Original universally closed theorem type | Published `Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eqStatement` |
| `LocalClassFieldTheory.localNormSubgroup_fieldRange_eq` | `Langlands.NYLL.LocalClassFieldTheory.localNormSubgroup_fieldRange_eq` |
| `LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroup` | `Langlands.NYLL.LocalClassFieldTheory.map_finiteNormSubgroup_eq_additiveNormSubgroup` |
| `CyclicCohomology.additiveNormSubgroup` | `Langlands.NYLL.CyclicCohomology.additiveNormSubgroup` |
| `AlgHom.fieldRange`, `AlgEquiv.ofInjectiveField`, and `IsGalois.of_algEquiv` | The same Mathlib declarations |

Worker 546 extracted the source theorem's proof, added the
`Langlands.NYLL` namespace prefix, and replaced the original theorem head
with the exact published closed proposition, introducing its complete
original telescope by `intro`. The remaining proof body and the
docstring are unchanged. The broad source imports are replaced by the
three focused modules listed above, the file documentation is focused
on this theorem, and unused namespace openings are removed. No other
worker's draft body is reused.

The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The current Library errata notes contain no matching NYLL erratum.

The original copyright, author and Apache-2.0 header are retained.
The original [LICENSE](../../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are unchanged;
their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Validation

The unconditional proof compiles with zero errors and warnings in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
Exact-declaration inspection reports a theorem with no universe
parameters, whose declared type is the closed proposition named above.
Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.
This development check is separate from independent semantic review
and the submission's exact-target validation.
