# Embedded finite-abelian norm transport: proposition target

This module defines the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eqStatement`.
With `open CyclicCohomology` in
`namespace Langlands.NYLL.LocalClassFieldTheory`, its exact body is

```lean
∀ (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  (i : L →ₐ[K] SeparableClosure K),
  ((finiteAbelianAbstractExtensionOfEmbedding K L i).normSubgroup
      (intrinsicAbsoluteUnits K)).map
    (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
    additiveNormSubgroup K L
```

For a finite abelian Galois extension `L/K` and a specified `K`-algebra
embedding `i` of `L` into the chosen separable closure of `K`, the target
identifies two additive subgroups of `Additive Kˣ`. The first is the
abstract norm subgroup of the embedded extension, mapped from the fixed
ambient coefficient group to base-field units by the inverse of the
canonical additive equivalence. The second is the ordinary field-norm
image, written additively. This is a proposition definition; it asserts
no proof.

The source objects are retained:

- `finiteAbelianAbstractExtensionOfEmbedding K L i` is the abstract finite
  abelian subextension attached to the actual `AlgHom.fieldRange i` in
  `SeparableClosure K`, with base `intrinsicAbstractBase K` (M402.001).
- `ClassFormation.FiniteAbelianSubextension.normSubgroup` is the actual
  `finiteNormSubgroup`, with quotient finiteness supplied locally by the
  packaged finite abelian extension (M296.030).
- `intrinsicAbsoluteUnits K` is the integral representation on the units
  of `SeparableClosure K` (M091.002).
- `baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)` identifies
  `Additive Kˣ` with the ambient coefficient subgroup fixed by the base
  closed fixing subgroup. Its inverse additive homomorphism is the map
  used in the conclusion (M096.001).
- `CyclicCohomology.additiveNormSubgroup K L` is
  `(LocalFieldTheory.localNormSubgroup K L).toAddSubgroup`, the range of
  the field norm on units with additive notation (M095.008).

The fields are in `Type`, hence universe zero, and the declaration has
no universe parameters. The order and kinds of the explicit `K`, `L`,
and `i` binders and all five instance binders are unchanged. There are no
valuation, topology, local-field, or norm-identity hypotheses.

## Source and changes

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean#L61-L81).
The docstring is at lines 61–63, the theorem head and type at lines
64–71, and its proof at lines 72–81. This is unit M402.002 of the
published [NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md).
The full source file was read; its SHA-256 is
`173d65750c2a18cc233fcc94d9fde94e88c7a42709cfb9c27e50bae8e971ba06`.

The enclosing `noncomputable section`,
`namespace LocalClassFieldTheory`, and namespace openings at lines
26–31 were inspected. There is no preceding `variable` or `universe`
declaration, so the displayed source telescope is complete.

| Source | Adapted |
| --- | --- |
| theorem `LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eq` | Prop definition `Langlands.NYLL.LocalClassFieldTheory.map_finiteAbelianAbstractExtension_normSubgroup_eqStatement` |
| `LocalClassFieldTheory.finiteAbelianAbstractExtensionOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianAbstractExtensionOfEmbedding` |
| `ClassFormation.FiniteAbelianSubextension.normSubgroup` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.normSubgroup` |
| `LocalClassFieldTheory.intrinsicAbsoluteUnits` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteUnits` |
| `LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` | `Langlands.NYLL.LocalClassFieldTheory.baseUnitsEquivGaloisAmbientFixed` |
| `CyclicCohomology.additiveNormSubgroup` | `Langlands.NYLL.CyclicCohomology.additiveNormSubgroup` |
| `IsAbelianGalois`, `FiniteDimensional`, `SeparableClosure`, and algebraic notation | the same Mathlib declarations and notation |

Worker 546 made these modifications: extract the theorem's type;
universally close its complete telescope in a `def ... : Prop`;
prefix the namespace with `Langlands.NYLL` and append `Statement` to the
name; retain the source docstring and `noncomputable` scope; replace the
source whole-module documentation with focused documentation; and drop
the unused `LocalFieldTheory`, `RamificationTheory`, `KummerTheory`,
and `ClassFormation` openings. The conclusion and hypotheses are
unchanged. No local, scoped, or global instance is introduced.

The source imports are replaced by Mathlib's `FieldTheory.Galois.Abelian`
and the focused adaptation modules
`FiniteAbelianSubextension.NormSubgroup.Definitions`,
`OrderReversal.U001.Definitions`,
`IntrinsicAbsoluteData.Initial.Definitions`,
`SeparableUnitsNorm.BaseUnits.Definitions`, and
`TateH0.NormImage.Definitions`, under their respective `Langlands.NYLL`
paths. These imports reuse the actual dependency declarations.

The source proof is omitted. It installs finite-dimensional and Galois
instances on the actual `AlgHom.fieldRange i`, uses
`localNormSubgroup_fieldRange_eq`, and applies
`map_finiteNormSubgroup_eq_additiveNormSubgroup`. Those proof dependencies
are not additional premises in this target. A separate proof task may
establish the published proposition.

The retained source snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable source erratum was found in the Library's errata notes.

The original copyright and author header is retained. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) in the Library
are unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No other worker's draft body was reused.

## Validation

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Exact-declaration
inspection reports a definition returning `Prop` with an empty universe
parameter list. This checks the proposition's elaboration; the module
supplies no proof of it.
