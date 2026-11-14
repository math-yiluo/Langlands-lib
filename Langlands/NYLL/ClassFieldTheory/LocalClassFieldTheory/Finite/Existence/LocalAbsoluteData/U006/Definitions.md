# NYLL M299.006: the intrinsic absolute base has finite index in `baseField`

This module ports the source instance
`LocalClassFieldTheory.intrinsicAbstractBase_index_finite` (unit M299.006) as
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase_index_finite`.

## Content

For every field `K : Type` (with `[Field K]`; `K` is an explicit section
variable, as in the source), the instance supplies

```lean
Finite ((baseField (intrinsicAbsoluteGalois K)).toSubgroup ⧸
  extensionSubgroup (baseField (intrinsicAbsoluteGalois K))
    (intrinsicAbstractBase K) (le_baseField (intrinsicAbstractBase K)))
```

The objects are the actual source objects:

- `intrinsicAbsoluteGalois K` is `Gal(SeparableClosure K / K)` with its Krull
  topology (M091.001).
- `baseField G` is the closed subgroup of `G` with underlying subgroup `⊤`, the
  distinguished base field of the abstract class formation (M010.003).
- `intrinsicAbstractBase K` is the closed fixing subgroup
  `closedFixingSubgroup K (SeparableClosure K) ⊥` of the bottom intermediate
  field, that is, the abstract field representing `K` itself (M091.003).
- `extensionSubgroup B L h` is `L.toSubgroup.subgroupOf B.toSubgroup` (M004.002),
  and `le_baseField L` proves `L.toSubgroup ≤ (baseField G).toSubgroup`
  (M010.005).

So the instance says that the quotient group of the full absolute Galois group
(as the subgroup `⊤`) by the fixing group of `K`, viewed inside it, is finite.
Mathematically the fixing group of the bottom field is the whole group, so the
quotient is trivial; as the source docstring says, the base "is absolutely
finite" in the abstract Galois-theoretic sense. The quotient is Mathlib's
`HasQuotient` quotient of the group `(baseField _).toSubgroup` by a subgroup,
and `Finite` is Mathlib's `Finite` class.

The implementation is the source one: the `finite` field of the published
finite abstract field `intrinsicFiniteAbstractBase K` (M091.006), whose
`field` is `intrinsicAbstractBase K` by definition (it is `@[reducible]`),
so `(intrinsicFiniteAbstractBase K).finite` has exactly the stated type.
Because `Finite` is a `Prop`-valued class, Lean compiles the instance as a
theorem-kind constant; the docstring, `noncomputable instance` modifiers and
the tactic body are nevertheless copied from the source. Proof irrelevance
means the instance cannot create a non-defeq instance diamond.

The instance's full telescope, checked with `#check` in a focused probe
(not part of this candidate), is

```lean
intrinsicAbstractBase_index_finite : ∀ (K : Type) [inst : Field K],
  Finite (↥↑(baseField (intrinsicAbsoluteGalois K)) ⧸
    extensionSubgroup (baseField (intrinsicAbsoluteGalois K))
      (intrinsicAbstractBase K) ⋯)
```

and with this module imported, `infer_instance` finds the instance for an
arbitrary field `K`.

## Existing Library instances

The task asked whether a published instance already supplies M299.006 with
exact source correspondence. None does:

- A focused probe importing only the Library module of
  `intrinsicFiniteAbstractBase` (which imports the modules of all objects in
  the type) failed to synthesize the instance above with `infer_instance`.
- The closest published instance is `Langlands.NYLL.PortInternal.M010.d125`
  (source M010.125, anonymous in the source), in
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`.
  It is generic over a bundled `K : FiniteAbstractField G` and states
  finiteness for the field projection `K.field`; instance search cannot
  reconstruct the bundled `intrinsicFiniteAbstractBase K` from the closed
  subgroup `intrinsicAbstractBase K`, so it does not apply, and it is a
  different source declaration.
- A search of the Library `.lean` files at base commit
  `c40a01345b2f4172fa41e07ff31644b40e695003` found no declaration
  `intrinsicAbstractBase_index_finite` and no other instance whose type
  mentions `intrinsicAbstractBase`.

Because the class is a `Prop`, adding this instance alongside `M010.d125`
creates no conflicting data.

## Reused Library declarations

| Source declaration (namespace) | Library declaration used | Module |
| --- | --- | --- |
| `LocalClassFieldTheory.intrinsicAbsoluteGalois` (M091.001) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `LocalClassFieldTheory.intrinsicAbstractBase` (M091.003) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` | same module |
| `LocalClassFieldTheory.intrinsicFiniteAbstractBase` (M091.006) | `Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase` | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Definitions` |
| `ClassFormation.baseField` (M010.003) | `Langlands.NYLL.ClassFormation.baseField` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions` |
| `ClassFormation.le_baseField` (M010.005) | `Langlands.NYLL.ClassFormation.le_baseField` | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs` |
| `CyclicCohomology.extensionSubgroup` (M004.002) | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions` |

The module imports only
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Base.Definitions`,
which transitively imports the modules of the other five declarations. The
published `le_baseField L` has type `le_baseFieldStatement L`, which unfolds
by definition to the source type; it is a proof argument, so the subgroup
is the same as in the source.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean>).
The complete file (117 lines) was read and its SHA-256 verified as
`87c3a6b1e9aa5fb2e8ae6602cb8fe6a0a5885f735fecb202c5582ff51567c000`.
The section variable `variable (K : Type) [Field K]` is line 105, the
docstring lines 107–108, the instance declaration lines 109–112 and its body
line 113. The header occupies lines 1–5, the imports lines 7–9,
`noncomputable section` line 22, the namespace line 24 and the `open` lines
26–27.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M299.006, `LocalClassFieldTheory.intrinsicAbstractBase_index_finite` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase_index_finite` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The row is listed in the public port plan
`notes/reuse/nyll-public-port/m289-m312.md`, section M299.

## Modifications and attribution

Worker 450 made these changes:

- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The instance keeps its source name and remains a global instance, as in the
  source (it is neither local nor scoped there).
- The source imports `Nyll...Finite.LocalReciprocity.Main`,
  `Nyll...Finite.LocalReciprocity.IntrinsicAbsoluteData` and
  `Nyll...AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification`.
  The port imports only the published module
  `IntrinsicAbsoluteData.Base.Definitions`. The broad
  `FiniteAbelianClassification` and `LocalReciprocity.Main` imports are not
  needed; the focused compilation of this module with the single import
  succeeded without warnings.
- The source opens `LocalFieldTheory RamificationTheory CyclicCohomology
  KummerTheory ClassFormation LocalClassFieldTheory`. The port opens only
  `CyclicCohomology` and `ClassFormation` (inside
  `Langlands.NYLL.LocalClassFieldTheory`), which resolve `extensionSubgroup`,
  `baseField` and `le_baseField` to the published declarations.
- The section variable `(K : Type) [Field K]`, with `K` explicit and in
  universe zero, the docstring, the modifiers `noncomputable instance`, the
  instance type and the body `exact (intrinsicFiniteAbstractBase K).finite`
  are copied unchanged. The `noncomputable section` wrapper is kept.
- The other declarations of the source file are not included: the structure
  `OpenFiniteIndexSubgroup` with its two instances and `ext` theorem
  (M299.001–.004, lines 29–65) are outside this task, and the theorem
  M299.005 (lines 67–103) is the separate statement module
  `LocalAbsoluteData/U005/Statements`.

## Candidate packaging

This module is not a candidate entry of its own. An instance of the
`Prop`-valued class `Finite` is a theorem-kind constant, and machine
validation rejected it as the entry of a definition candidate
(`0f89efea-47a9-458e-8711-473dacdce8a3`: "A definition artifact must contain
a Lean definition or defined type"). It therefore travels as a helper module
in the `repository_paths` of the candidate whose entry is the M299.005
statement `abstractFixedField_isGalois_of_base_normalStatement`
(`LocalAbsoluteData/U005/Statements`). One review covers both units. The
Library precedent is the M096.003 `Finite` instance
`baseFixingExtensionQuotient_finite`
(`LocalReciprocity/SeparableUnitsNorm/Finite/Definitions`), which travelled
with a definition entry. Task 6078 revision 2 records this packaging. The
module's Lean content is unchanged from the rejected candidate.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright, the
authorship line including OpenAI Codex assistance and the Apache-2.0 notice,
and records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files; their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
