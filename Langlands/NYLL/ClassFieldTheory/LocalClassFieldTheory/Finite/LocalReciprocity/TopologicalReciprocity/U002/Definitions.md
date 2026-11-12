# Integer-unit norm and its image subgroup

`Langlands.NYLL.PortInternal.M257.d002` is the actual monoid homomorphism
from the units of the valuation-integer subring of `L` to `Kˣ` obtained by
first applying the published inclusion
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits L`
and then the published field-unit norm
`Langlands.NYLL.LocalFieldTheory.normUnits K L`.
`Langlands.NYLL.PortInternal.M257.d003` is its image subgroup of `Kˣ`.
Their complete interfaces, in the displayed namespace, are:

```lean
universe u
(K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel L] :
  𝒪[L]ˣ →* Kˣ
(K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel L] :
  Subgroup Kˣ
```

The fields share the same arbitrary universe, as in the source. The field
parameters are explicit. Only the valuation on `L` is required. There is no
valuation on `K`, topology, local-field assumption, finite-dimensionality or
separability premise. These definitions assert no compactness, openness,
surjectivity or kernel result and introduce no instance.

## Source correspondence and modifications

This is the focused pair M257.002–003 from Naganori Yamaguchi's
ClassFieldTheory at commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`,
lines 43–57 (common universe at line 45). The original file SHA-256 is
`28cfb0b56b885089511a7372bfe3bf5e80d444fb91d1e982ba0b5647d26d0108`.

| Source unit and name | Public adaptation |
| --- | --- |
| M257.002, private `LocalClassFieldTheory.integerUnitNormMap`, lines 47–51 | `Langlands.NYLL.PortInternal.M257.d002` |
| M257.003, private `LocalClassFieldTheory.integerUnitNormSubgroup`, lines 53–57 | `Langlands.NYLL.PortInternal.M257.d003` |

The source-private definitions receive stable internal names according to the
published port partition. Their documentation strings, common universe,
parameter order, instances and bodies are preserved, with references qualified
to their published names and `integerUnitNormMap` renamed to `d002` in the
second body. The source's namespace and section wrappers are replaced by the
single `Langlands.NYLL.PortInternal.M257` namespace and its noncomputable
section. The module prose is focused on this pair. The source's `ValuativeRel`
scope is retained; unused source scopes and opened namespaces are omitted.

The full source imports are replaced by the already published focused
`Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions`
and
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`.
No construction of a field-unit norm or inclusion is duplicated. A search of
the current Library found no existing integer-unit norm composite or image
subgroup matching these units.

The focused draft compilation and exact-signature checks
`fff2e22f-cc3a-4898-97a7-91e4cddecda3` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` succeeded without errors or warnings.
The checks assign both declarations to precisely the displayed full dependent
function types, and verify by `rfl` that their bodies equal the original
composition and range after name adaptation. Thus the smaller imports suffice;
M254, M158, M255, M256 and the source-local quotient topology M257.001 are not
dependencies of these definitions. This does not discharge those units when
other declarations require them. Compactness and the other remaining source
theorems need their own target and exact-proof publications.

## Attribution

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
No applicable project or Library errata file was found. The original copyright
and author header credits Naganori Yamaguchi (assisted by OpenAI Codex) and is
retained verbatim. Worker 120 performed this extraction and documented the
modifications on 10 November 2026. No patch10 code or other worker's draft is
copied into this pair. The existing Apache-2.0 files are
`licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
There is no NOTICE entry specific to TopologicalReciprocity.
