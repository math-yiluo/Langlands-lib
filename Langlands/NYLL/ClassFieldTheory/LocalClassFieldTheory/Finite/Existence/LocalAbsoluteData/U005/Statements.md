# NYLL M299.005: base normality makes the abstract fixed field Galois (statement)

This module defines the Prop-valued target
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normalStatement`,
the statement phase of source row M299.005. It packages the complete
signature of the source theorem
`LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normal` as a `def`
returning `Prop` and supplies no proof. A later `lean.proof@1` child, routed by
Worker 303, is expected to prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normal`
as a theorem of type
`abstractFixedField_isGalois_of_base_normalStatement K H hnormal`.

## Parameters

The definition has exactly the source theorem's binders, in the source order
and with the source binder kinds:

```lean
(K : Type) [Field K]
(H : ClosedSubgroup (Gal(SeparableClosure K/K)))
(hnormal :
  (extensionSubgroup
    (baseField (Gal(SeparableClosure K/K))) H
    (le_baseField H)).Normal)
```

- `K` is an arbitrary field in `Type` (universe zero), as in the source. No
  valuation, topology, completeness or nonarchimedean hypothesis is placed on
  `K`; the source word "local" in the docstring refers to the intended use, not
  to a hypothesis.
- `Gal(SeparableClosure K/K)` is Mathlib's group `SeparableClosure K ≃ₐ[K]
  SeparableClosure K` with its Krull topology, where `SeparableClosure K` is
  Mathlib's chosen separable closure (the separable closure of `K` in
  `AlgebraicClosure K`). It is definitionally the Library's
  `intrinsicAbsoluteGalois K`, which the source and this port spell out.
- `H` is a Mathlib `ClosedSubgroup` of that topological group.
- `baseField G` is the closed subgroup with underlying subgroup `⊤` (the
  distinguished base field of the abstract class formation, represented
  contravariantly by the whole group). `le_baseField H` is the proof that
  `H.toSubgroup ≤ (baseField G).toSubgroup`.
- `extensionSubgroup B H _` is `H.toSubgroup.subgroupOf B.toSubgroup`, the
  subgroup `G_H` regarded inside `G_B`. The hypothesis `hnormal` says that it is
  a normal subgroup of `(baseField G).toSubgroup`. Since that subgroup is `⊤`,
  this is normality of `H` in the whole absolute Galois group, but the
  hypothesis keeps the source's relative form.

As in the source theorem, the conclusion does not mention `hnormal`; it is a
hypothesis of the target, so the definition binds it and Lean reports an
unused-variable lint warning for it. The proof child receives it as the
corresponding binder. This is the same parameterized convention as the
published `abstractRelativeFixedField_isGaloisStatement` (M099.012), whose
`hnormal` is likewise a binder not mentioned in its conclusion.

## Conclusion

```lean
IsGalois K (abstractFixedField K (SeparableClosure K) H)
```

`abstractFixedField K (SeparableClosure K) H` is the intermediate field
`IntermediateField.fixedField H.toSubgroup` of `SeparableClosure K` over `K`;
it uses Mathlib's instance `IsGalois K (SeparableClosure K)` (via
`IsSepClosure.isGalois`). The conclusion is Mathlib's `IsGalois` for this
intermediate field over `K`. Mathematically: if a closed subgroup of the
absolute Galois group is normal, its fixed field is a Galois extension of `K`.

A focused probe check (not part of this candidate) confirmed that
`abstractFixedField_isGalois_of_base_normalStatement K H hnormal` is
definitionally `IsGalois K (abstractFixedField K (SeparableClosure K) H)`
(by `rfl`), and that the source proof (lines 77–103) closes the target over
the published Library, with the source step `rw [mem_extensionSubgroup_iff]`
replaced by `rfl` because `extensionSubgroup` is an abbreviation for
`subgroupOf`. That proof uses only `propext`, `Classical.choice` and
`Quot.sound`. The proof is not submitted here.

## Reused Library and Mathlib declarations

| Source declaration (namespace) | Declaration used | Module |
| --- | --- | --- |
| `LocalClassFieldTheory.abstractFixedField` (M099.001) | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| `ClassFormation.baseField` (M010.003) | `Langlands.NYLL.ClassFormation.baseField` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions` |
| `ClassFormation.le_baseField` (M010.005) | `Langlands.NYLL.ClassFormation.le_baseField` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| `CyclicCohomology.extensionSubgroup` (M004.002) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |
| Mathlib `SeparableClosure`, `ClosedSubgroup`, `IsGalois`, `Subgroup.Normal` | the same Mathlib names | `Mathlib.FieldTheory.IsSepClosed` and the Mathlib imports of the modules above |

The published `le_baseField H` has type `le_baseFieldStatement H`, which unfolds
by definition to the source type `H.toSubgroup ≤ (baseField G).toSubgroup`;
the argument is a proof, so `extensionSubgroup` receives the same subgroup as in
the source.

A search of the Library `.lean` files at base commit
`c40a01345b2f4172fa41e07ff31644b40e695003` found no declaration
`abstractFixedField_isGalois_of_base_normal` or other statement of this
implication for a base-normal closed subgroup of `Gal(SeparableClosure K/K)`.
The closest published target is
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedField_isGaloisStatement`
(M099.012), the relative version for a pair of closed subgroups of
`Gal(Ω/k)` with `IsGalois` of the relative fixed field over
`abstractFixedField k Ω K`; it is not the absolute statement over `K` and is
not reused. Mathlib's `InfiniteGalois.normal_iff_isGalois` is the underlying
infinite Galois correspondence the source proof uses; it is stated for
intermediate fields, not for `ClosedSubgroup`s with the abstract-base
hypothesis, so it is not a substitute target.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean>).
The complete file (117 lines) was read and its SHA-256 verified as
`87c3a6b1e9aa5fb2e8ae6602cb8fe6a0a5885f735fecb202c5582ff51567c000`.
The docstring occupies lines 67–68 and the signature lines 69–76; the proof
occupies lines 77–103 after `:= by` on line 76. The header occupies lines 1–5,
the imports lines 7–9, `noncomputable section` line 22, the namespace line 24
and the `open` lines 26–27.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M299.005, `LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normal` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normalStatement`, Prop target (this unit) |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normal`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The row is listed in the public port plan
`notes/reuse/nyll-public-port/m289-m312.md`, section M299.

## Modifications and attribution

Worker 450 made these changes to the source theorem:

- The theorem becomes a `def` returning `Prop` with the suffix `Statement`.
  Its binders `(K : Type) [Field K]`, `(H : ...)` and `(hnormal : ...)` are kept
  with the same names, types, order and binder kinds; the result type is the
  source conclusion. The proof (lines 77–103) is omitted for the separate proof
  phase. The docstring is copied unchanged.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports `Nyll...Finite.LocalReciprocity.Main`,
  `Nyll...Finite.LocalReciprocity.IntrinsicAbsoluteData` and
  `Nyll...AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification`.
  The port imports instead `Mathlib.FieldTheory.IsSepClosed` (for
  `SeparableClosure` and its `IsGalois` instance) and the four published
  Library modules in the table above. In particular, the broad
  `FiniteAbelianClassification` and `LocalReciprocity.Main` imports are not
  needed for this statement; the focused compilation of this module with the
  smaller imports succeeded.
- The source opens `LocalFieldTheory RamificationTheory CyclicCohomology
  KummerTheory ClassFormation LocalClassFieldTheory`. The port opens only
  `CyclicCohomology` and `ClassFormation` (inside
  `Langlands.NYLL.LocalClassFieldTheory`), which resolve `extensionSubgroup`,
  `baseField` and `le_baseField` to the published declarations.
- The source's `noncomputable section` is omitted; the statement is a
  proposition. The source structure `OpenFiniteIndexSubgroup` with its
  instances and `ext` theorem (M299.001–.004, lines 29–65) and the instance
  M299.006 (lines 105–113) are not part of this unit. M299.006 is the separate
  module `LocalAbsoluteData/U006/Definitions` with its own Markdown. This
  module does not import it.

## Candidate packaging

The candidate whose entry is this statement also carries the M299.006
instance module `LocalAbsoluteData/U006/Definitions` (Lean and Markdown) as a
helper module in its `repository_paths`, so one review covers both units of
Task 6078. The instance could not be its own candidate: an instance of the
`Prop`-valued class `Finite` is a theorem-kind constant, and machine
validation rejected it as a definition candidate
(`0f89efea-47a9-458e-8711-473dacdce8a3`). The Library precedent is the
M096.003 `Finite` instance `baseFixingExtensionQuotient_finite`, which was
published as a helper module of a definition entry. Task 6078 revision 2
records this packaging.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files; their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
