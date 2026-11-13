# Continuity of the intrinsic-to-ambient base equivalences: statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M281.002 and M281.003:

- `intrinsicBaseEquivAmbientFixedField_continuousStatement`, for the source
  theorem `intrinsicBaseEquivAmbientFixedField_continuous`;
- `intrinsicBaseEquivAmbientEmbeddedField_continuousStatement`, for the source
  theorem `intrinsicBaseEquivAmbientEmbeddedField_continuous`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_continuous`
and
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous`.

They assert that the two published multiplicative equivalences of source rows
M273.004 and M273.006 (module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`)
are continuous. Each domain and codomain is a subgroup of an absolute Galois
group `Gal(SeparableClosure _ / _)`, with the subspace topology of Mathlib's
Krull topology on that Galois group.

## The proposition `intrinsicBaseEquivAmbientFixedField_continuousStatement`

It universally quantifies, as in the source,

```lean
(K : Type) [Field K]
  (H : Langlands.NYLL.ClassFormation.FiniteAbstractField
    Gal(SeparableClosure K/K))
```

So `K` is a field in `Type` (universe zero, as in the source) and `H` is a
finite abstract field of `Gal(SeparableClosure K / K)`: a closed subgroup
`H.field` together with the finiteness of the left-coset quotient of the base
field by it. It then introduces, as in the source,

```lean
let F := abstractFixedField K (SeparableClosure K) H.field
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
```

`F` is the fixed field of `H.field`, an intermediate field of
`SeparableClosure K / K`. The local instance is the algebra structure of the
intermediate field `separableClosure F (AlgebraicClosure F)`, which is how
Mathlib defines `SeparableClosure F`. The proposition then quantifies over an
`F`-algebra isomorphism `e : SeparableClosure F ≃ₐ[F] SeparableClosure K` and
concludes

```lean
Continuous (intrinsicBaseEquivAmbientFixedField K H e)
```

that is, the map `(intrinsicAbstractBase F).toSubgroup → H.field.toSubgroup`
underlying the published equivalence is continuous.

## The proposition `intrinsicBaseEquivAmbientEmbeddedField_continuousStatement`

It universally quantifies, as in the source,

```lean
(K F : Type) [Field K] [Field F]
  [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
  (i : F →ₐ[K] SeparableClosure K)
```

So `F / K` is a finite separable extension of fields in `Type` and `i` is a
`K`-algebra embedding of `F` into `SeparableClosure K`. There is no valuation,
topology or local-field hypothesis on the fields. It then introduces, as in
the source,

```lean
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
```

the second making `SeparableClosure K` an `F`-algebra through `i`. It
quantifies over `e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these
structures and concludes

```lean
Continuous (intrinsicBaseEquivAmbientEmbeddedField K F i e)
```

that is, the map from `(intrinsicAbstractBase F).toSubgroup` to the closed
subgroup of `Gal(SeparableClosure K / K)` fixing `i(F)` underlying the
published equivalence is continuous.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M273.004, `LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`) |
| M273.006, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` (same module) |
| M010.121, `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`, imported through the U004 module) |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`, imported through the U004 module) |

The types of the two equivalences also use the published
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (M091.003) and
`Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (M087.001), which
the statements do not name.

## Relation to other Library and Mathlib declarations

No published declaration states either proposition: the two equivalences
exist only in this port. Related published results, which a proof may use,
are the following.

- `Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongrStatement`
  (source row M001.001, module
  `Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Statements`,
  proved in the paired `Proofs` module) states that `AlgEquiv.autCongr e` is
  continuous for the Krull topologies. This is one ingredient of the first
  equivalence, not its continuity.
- `Langlands.ClassFieldTheory.Local.closureSubgroupEquiv`
  (module `Langlands.ClassFieldTheory.Local.ClosureRestrictionTransport`)
  is a homeomorphic group isomorphism between the absolute Galois group of an
  intermediate field `E` of an algebraic closure (in characteristic zero)
  and `E.fixingSubgroup`. It is a different map between different groups.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean>).
The complete file was read and its SHA-256 verified as
`d8403d819db83b085b6fad6144c82340f414f44f5675e495b83e79ffd28ee1a1`.
The M281.002 docstring occupies lines 122–123 and its signature lines
124–132; its proof occupies lines 133–149. The M281.003 docstring occupies
lines 151–152 and its signature lines 153–164; its proof occupies lines
165–285. The header occupies lines 1–5, the module docstring lines 15–20,
the `noncomputable section` line 24, the namespace line 26 and the `open`
lines 28–30.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M281.002, `LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_continuous` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_continuousStatement`, closed Prop target |
| M281.003, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuousStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientFixedField_continuous` and `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_continuous`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase. The binders,
  local `let`/`letI` data and conclusions are otherwise the source text.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`,
  and `FiniteAbstractField` is written fully qualified instead of being
  reached through the source `open ClassFormation` line.
- The source imports are replaced by the Library module that publishes the
  two equivalences, which imports the other declarations used.
- The `noncomputable section` and the `open` lines are omitted. All other
  declarations of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M281.002 and M281.003 statement targets. Their
proofs and the other rows of the source file are not part of this unit.
