# NYLL M040.022: total ramification of a finite Galois extension by degree images

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.isTotallyRamified_iff_image_leStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.isTotallyRamified_iff_image_le`.
The theorem's type is exactly that proposition applied to its source
parameters, `isTotallyRamified_iff_image_leStatement L D`.

## Target and parameters

The theorem has, in this order, implicit `G : Type u`, the instances
`[Group G]` and `[TopologicalSpace G]`, implicit `K : ClosedSubgroup G` (the
source section variable), then explicit `L : FiniteGaloisSubextension K` and
`D : DegreeData G`: the statement's telescope with the same binder kinds and
its single universe parameter `u`. No premise is added. Unfolding the
proposition gives

```lean
L.IsTotallyRamified D ↔
  K.toSubgroup.map D.degree.toMonoidHom ≤
    L.field.toSubgroup.map D.degree.toMonoidHom
```

that is, the finite Galois subextension `L` of `K` is totally ramified for
the degree data `D` if and only if the image of `K` under the degree
homomorphism is contained in the image of the top-field subgroup `L.field`.

## Implemented proof

The complete proof is the source term

```lean
  L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D
```

It applies the published M010.076 theorem
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.isTotallyRamified_iff_image_le`
to the underlying finite abstract extension `L.toFiniteAbstractExtension`
(the published M040.003 definition, with `field := L.field`, `base := K`,
`below := L.below` and `finiteQuotient := L.finite`). That theorem has type
`DegreeData.FiniteAbstractExtension.isTotallyRamified_iff_image_leStatement
L.toFiniteAbstractExtension D`, namely

```lean
L.toFiniteAbstractExtension.IsTotallyRamified D ↔
  L.toFiniteAbstractExtension.base.toSubgroup.map D.degree.toMonoidHom ≤
    L.toFiniteAbstractExtension.field.toSubgroup.map D.degree.toMonoidHom
```

Lean accepts it at the target type by definitional unfolding: the published
M040.006 `FiniteGaloisSubextension.IsTotallyRamified L D` is by definition
`L.toFiniteAbstractExtension.IsTotallyRamified D`, and the projections
`base` and `field` of `L.toFiniteAbstractExtension` reduce to `K` and
`L.field`. No other theorem is used.

## Dependencies

The direct imports are
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements`,
which supplies the target statement and, through its Definitions module, the
published `FiniteGaloisSubextension` structure, `toFiniteAbstractExtension`
and `IsTotallyRamified`; and
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Supplement.U076.Proofs`,
which supplies the published M010.076 theorem used by the source proof. Both
are in the Library; no published Lean/Markdown pair is changed.

## Pinned source and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
whose whole-file SHA-256
`c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`
Worker 744 recomputed from the retained copy under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`
on 16 November 2026 UTC; it matches the
[port partition](../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m040),
which records no patch10 edit for M040. The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; the
attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The passage is
[lines 204–210](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean#L204-L210):
docstring at line 204, theorem name and telescope at 205–206, assertion at
207–209 and proof term at 210; the next unit starts at line 212 (docstring)
and 215 (declaration). The enclosing context is namespace `ClassFormation`
(line 17), `noncomputable section` (line 25), `universe u` (line 27),
section `GroupOnly` with its group variables (lines 29–31), namespace
`FiniteGaloisSubextension` (line 44) and the variable `{K : ClosedSubgroup G}`
(line 46).

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `FiniteGaloisSubextension.isTotallyRamified_iff_image_le` | Published `FiniteGaloisSubextension.isTotallyRamified_iff_image_leStatement` |
| Proof `FiniteGaloisSubextension.isTotallyRamified_iff_image_le` | This theorem, same adapted name, same proof term |
| `DegreeData.FiniteAbstractExtension.isTotallyRamified_iff_image_le` (M010.076) | Published theorem of the same adapted name |
| `FiniteGaloisSubextension`, `toFiniteAbstractExtension`, `IsTotallyRamified` | Existing published data (M040.001, M040.003, M040.006) |

Modifications by Worker 744 on 16 November 2026 UTC: prefix the namespace
with `Langlands.NYLL`; replace the source import with the published
statement module and the published M010.076 proof module; give the theorem
the published proposition applied to its parameters as its type; omit the
source `noncomputable section`, `open KummerTheory`, `open CyclicCohomology`,
the `GroupOnly` section and all other source declarations. The original
docstring and proof term are retained.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 744's dated modification
record. Worker 744 extracted this proof directly from the pinned original and
the published statement; no project draft was reused and there are no
project coauthors. The statement pair (Worker 4918) and the M010.076 proof
(Worker 79) are imported unchanged; no imported Library file is edited.

The unchanged inherited [LICENSE](../../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained in
`repository_paths`. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`: Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A development
`lean_check` compiled the module with no errors or warnings, and declaration
inspection reported only the axioms `propext`, `Classical.choice` and
`Quot.sound`, with the single universe parameter `u`. Development
compilation is separate from acceptance: publication under `lean.proof@1`
also requires the Lake, kernel and exact-target checks, independent semantic
review and Integrator publication.

This is an abstract subgroup result covering only M040.022. It supplies no
host class-formation, cup-product, transfer, Tate-cohomology or reciprocity
theorem.
