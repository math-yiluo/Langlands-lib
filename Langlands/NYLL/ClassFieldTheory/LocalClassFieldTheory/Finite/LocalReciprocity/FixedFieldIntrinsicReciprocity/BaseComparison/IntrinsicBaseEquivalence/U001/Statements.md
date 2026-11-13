# Finite quotient for an embedded finite extension: statement

This module defines the closed proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFiniteStatement`,
the statement phase of source row M273.001. It packages the complete source
theorem signature as a `def` returning `Prop` and supplies no proof. A later
proof child will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite`.

## Parameters

The proposition universally quantifies, in the source order,

```lean
(K F : Type) [Field K] [Field F]
  [Algebra K F] [FiniteDimensional K F]
  (i : F →ₐ[K] SeparableClosure K)
```

Both fields are in `Type` (universe zero), as in the source. `F` is an
arbitrary finite extension of `K`, and `i` is a `K`-algebra embedding of `F`
into Mathlib's separable closure `SeparableClosure K`. There is no
separability, valuation, topology or local-field hypothesis on `K` or `F`.
The Galois group `Gal(SeparableClosure K / K)` carries Mathlib's Krull
topology. Mathlib's instance `IsSepClosure.isGalois` supplies
`IsGalois K (SeparableClosure K)`, which the closed fixing subgroup below
requires.

## Conclusion

The proposition introduces the abbreviation

```lean
let H₀ :=
  Langlands.NYLL.RamificationTheory.closedFixingSubgroup K (SeparableClosure K)
    (AlgHom.fieldRange i)
```

the closed subgroup of `Gal(SeparableClosure K / K)` fixing the image
`i(F)`, viewed as an intermediate field of `SeparableClosure K / K`. It then
concludes

```lean
Finite
  ((Langlands.NYLL.ClassFormation.baseField
      Gal(SeparableClosure K / K)).toSubgroup ⧸
    H₀.toSubgroup.subgroupOf
      (Langlands.NYLL.ClassFormation.baseField
        Gal(SeparableClosure K / K)).toSubgroup)
```

Here `Langlands.NYLL.ClassFormation.baseField G` is the closed subgroup `⊤`
of `G`. So the statement says: the set of left cosets of `H₀`, taken inside
the whole group `Gal(SeparableClosure K / K)` viewed as its top subgroup, is
finite. In other words, the subgroup fixing `i(F)` has finite index.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`) |

The Library `closedFixingSubgroup k Ω K` is
`⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩` for a Galois
extension `Ω / k`, as in the source.

The source statement also uses the abbreviation M004.002
`CyclicCohomology.extensionSubgroup K L hLK := L.toSubgroup.subgroupOf
K.toSubgroup` and the theorem M010.005 `ClassFormation.le_baseField`. Neither
is published as a Lean declaration. The abbreviation ignores its inclusion
proof `hLK`, so this module writes its body directly as `H₀.toSubgroup.subgroupOf
(baseField _).toSubgroup` and no longer needs the proof `le_baseField H₀`.
The published Library module
`Langlands/NYLL/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields/AbstractExtension/Definitions.lean`
makes the same replacement of `extensionSubgroup` by its `Subgroup.subgroupOf`
body. A private check, not part of this submission, copies the source
`extensionSubgroup` and `le_baseField` verbatim. It confirms by `Iff.rfl` and
`rfl` that this proposition is definitionally the source statement.

## Relation to other Library and Mathlib declarations

No published declaration states this proposition. The closest are:

- `Langlands.LocalClassField.absoluteFixingFiniteIndex` in
  `Langlands/ClassFieldTheory/Local/Transfer.lean`. It states
  `E.fixingSubgroup.FiniteIndex` for a finite-dimensional intermediate field
  `E` of `AlgebraicClosure K` over a perfect field `K`. That is a different
  closure, an extra perfectness hypothesis, an intermediate field rather than
  the image of an embedding, and a `FiniteIndex` conclusion rather than
  finiteness of a quotient of `⊤`.
- Mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index`, which
  states `Module.finrank F L = L.fixingSubgroup.index` for an intermediate
  field `L` of a Galois extension. It concerns the index, not the finiteness
  of this quotient type.

The proposition can be derived from Mathlib facts: the fixing subgroup of a
finite-dimensional intermediate field is open (`IntermediateField.fixingSubgroup_isOpen`),
and a compact group has only finitely many cosets of an open subgroup. The
private check also proves it this way, using only Mathlib. This module still
publishes it in source form because later source rows (M273.002 onward) use
it by name.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean>).
The complete file was read and its SHA-256 verified as
`0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`.
The selected docstring and signature occupy lines 28–42; the theorem begins
at line 30, and its proof occupies lines 43–77 after `:= by` on line 42. The header occupies lines
1–5, the module docstring lines 11–16, the `noncomputable section` line 20,
the namespace line 22 and the `open` lines 24–26. The source abbreviation
`extensionSubgroup` is in
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean` (SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`), lines
51–54, and `le_baseField` is in
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` (SHA-256
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`), lines
61–63.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M273.001, `LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFiniteStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`,
  and the published names `closedFixingSubgroup` and `baseField` are written
  fully qualified instead of being reached through the source `open` lines.
- `extensionSubgroup (baseField _) H₀ (le_baseField H₀)` is replaced by its
  body `H₀.toSubgroup.subgroupOf (baseField _).toSubgroup`, as described
  above.
- The source imports are replaced by the two Library modules that provide
  `baseField` and `closedFixingSubgroup`, and by
  `Mathlib.FieldTheory.IsSepClosed`, which provides `SeparableClosure`.
- The `noncomputable section` and the `open` lines are omitted. All other
  declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M273.001 statement target. Its proof and the
other rows of the source file (M273.002–M273.009) are not part of this unit.
