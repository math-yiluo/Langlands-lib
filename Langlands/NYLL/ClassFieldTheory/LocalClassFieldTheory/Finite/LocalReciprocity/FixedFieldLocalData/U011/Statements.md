# The chosen valuation rings on a finite fixed field: statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phase of source row
M272.011:

- `localSeparableValuationSubring_eq_comap_abstractFixedFieldEquivStatement`,
  for the source theorem
  `localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It is not proved here. A later proof child will prove it under
the name
`Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv`.

The proposition concerns the valuation ring `localSeparableValuationSubring K`
of `SeparableClosure K` that the finite local reciprocity construction
chooses for a nonarchimedean local field `K` (source row M249.006,
published). It is the companion of the published M272.006 statement
`localSeparableValuationSubring_eq_comap_finiteExtensionEquivStatement`
(module `...LocalReciprocity.FixedFieldLocalData.U006.Statements`). There the
finite extension `F` of `K` is an arbitrary local field with an embedding
into `SeparableClosure K`. Here `F` is the fixed field, inside
`SeparableClosure K`, of an abstract field finite over the base, with the
spectral local-field structure.

## The proposition

It universally quantifies, as in the source,

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (H : FiniteAbstractField (Gal(SeparableClosure K / K)))
```

So `K` is a nonarchimedean local field in `Type` (universe zero, as in the
source). `H` is an element of the published structure
`FiniteAbstractField` (source row M010.121): a closed subgroup `H.field` of
the absolute Galois group `Gal(SeparableClosure K / K)` with a proof
`H.finite` that the quotient of the base by its extension subgroup is
finite. Write

```lean
F := abstractFixedField K (SeparableClosure K) H.field
```

for the fixed field of `H.field` in `SeparableClosure K`, an intermediate
field of `SeparableClosure K / K` (source row M099.001), used as a type. The
source writes `F` with the file's private abbreviation `finiteFixedField K H`
(source lines 32–36); the port writes the unfolded term each time (see
below). The proposition then introduces

```lean
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
```

This is the source's `local instance finiteFixedFieldSeparableClosureAlgebra`
(source lines 38–44): the algebra structure of the intermediate field
`separableClosure F (AlgebraicClosure F)`, which is how Mathlib defines
`SeparableClosure F`. It quantifies over an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for this structure and the
inclusion of `F` in `SeparableClosure K`. It then introduces, as in the
source, four local instances on `F`:

```lean
letI : FiniteDimensional K F :=
  abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
letI : NontriviallyNormedField F :=
  Langlands.LocalField.FiniteExtension.normedField K F
letI : ValuativeRel F :=
  Langlands.LocalField.FiniteExtension.valuativeRel K F
letI : IsNonarchimedeanLocalField F :=
  Langlands.LocalField.FiniteExtension.isLocalField K F
```

- The first is the published theorem `abstractFixedField_finiteDimensional`
  (source row M099.005, proved in the Library): `F` is finite over `K`.
- The second, third and fourth give `F` the spectral norm extending the
  norm of `K`, the valuative relation of that spectral valuation, and the
  proof that `F` is then a nonarchimedean local field. The topology on `F`
  is the one of the spectral norm. The source uses its own definitions
  `finiteExtensionSpectralNormedField`, `finiteExtensionSpectralValuativeRel`
  and `finiteExtensionSpectralIsNonarchimedeanLocalField` (source rows
  M270.003, M270.007 and M270.008). The port uses the published Library
  declarations that cover them, as the published M270.009 statement
  `Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement`
  (module `...NonarchimedeanLocalField.FiniteExtensionTopology.U009.Statements`)
  already does. Its Markdown records that a review found the Library norm
  and relation definitionally equal to the source definitions. The class
  `IsNonarchimedeanLocalField` is a `Prop`, so the choice of proof in the
  fourth instance does not matter.

The conclusion is

```lean
localSeparableValuationSubring F =
  (localSeparableValuationSubring K).comap e.toRingHom
```

So the ring homomorphism underlying `e` pulls the chosen valuation ring of
`SeparableClosure K` back to the chosen valuation ring of
`SeparableClosure F`, where the latter is formed for the spectral
local-field structure on `F`.

In the Lean file `F` is written out as
`abstractFixedField K (SeparableClosure K) H.field` at each occurrence,
coerced to a type.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.006, `LocalClassFieldTheory.localSeparableValuationSubring` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions`) |
| M099.005, `LocalClassFieldTheory.abstractFixedField_finiteDimensional` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_finiteDimensional` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.U005.Proofs`) |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (module `...LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`, imported through the M099.005 module) |
| M010.121, `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`) |
| M270.003, `LocalFieldTheory.finiteExtensionSpectralNormedField` | `Langlands.LocalField.FiniteExtension.normedField` (module `Langlands.LocalField.FiniteExtension`) |
| M270.007, `LocalFieldTheory.finiteExtensionSpectralValuativeRel` | `Langlands.LocalField.FiniteExtension.valuativeRel` (same module) |
| M270.008, `LocalFieldTheory.finiteExtensionSpectralIsNonarchimedeanLocalField` | `Langlands.LocalField.FiniteExtension.isLocalField` (same module) |
| M272.001, private abbreviation `LocalClassFieldTheory.finiteFixedField` | unfolded to `abstractFixedField K (SeparableClosure K) H.field` |
| M272.002, local instance `LocalClassFieldTheory.finiteFixedFieldSeparableClosureAlgebra` | its body, supplied by the first `letI` |

`FiniteAbstractField` is reached through the source's
`open ClassFormation` line, which inside the namespace
`Langlands.NYLL.LocalClassFieldTheory` opens
`Langlands.NYLL.ClassFormation`. `IsNonarchimedeanLocalField`,
`ValuativeRel`, `SeparableClosure`, `separableClosure`, `AlgebraicClosure`
and the instance `IsGalois K (SeparableClosure K)` used by
`abstractFixedField` are Mathlib declarations.

## Development check of the source proof

A development check compiled the source proof (source lines 745–782)
against this proposition with no errors or warnings, using only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. Its only changes were
the Library names: `localSeparableValuationSubring_comap_embedding`
(M265.012), `hasExtension_valuation_of_valuationSubring_pullback` (M110.004),
`finiteExtensionSpectralValuation_hasExtension` (M270.009),
`localCompleteDVF` (M248.001) and
`localSeparableValuationSubring_eq_of_hasExtension` (M249.009), all proved or
defined in the Library at commit
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`, together with the same Library
replacements for M270.003, M270.007 and M270.008 as above. This only
confirms that the statement is formed as in the source; the proof belongs to
the later proof child.

## Relation to other Library and Mathlib declarations

The whole Library at commit `4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` was
searched. No published declaration states this proposition. The related
declarations are:

- the published M272.006 statement named above, the same conclusion for a
  finite separable extension `F` of local fields with its own valuation
  satisfying `Valuation.HasExtension`, and an embedding
  `i : F →ₐ[K] SeparableClosure K`. The present proposition is not an
  instance of it as stated: here `F` is a subfield of `SeparableClosure K`
  with the spectral structure, the algebra structure on
  `SeparableClosure K` is the inclusion, and no `Valuation.HasExtension`
  hypothesis is assumed;
- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_comap_embeddingStatement`
  (M265.012, `...LocalReciprocity.UnramifiedComparison.ComapEmbeddingStatement`),
  which says that the chosen valuation ring of `SeparableClosure K` pulls
  back along an embedding of a finite separable extension `L` to the
  valuation ring of `L`;
- `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_of_hasExtensionStatement`
  (M249.009, `...LocalReciprocity.LocalResidueDatum.U009.Statements`), which
  says that every valuation ring `B` of `SeparableClosure K` whose valuation
  extends the valuation `(localCompleteDVF K).valuation` of `K` is
  `localSeparableValuationSubring K`.

The source proof combines the last two.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldLocalData.lean>).
The complete file was read and its SHA-256 verified as
`e629ef932276f009cee72064f4b1dffe03aa262dcd391da5a6e98c4c9008f3cd`.
The M272.011 docstring occupies lines 718–720 and its signature lines
721–744; its proof occupies lines 745–782. The `open … in` prefix on lines
715–717 is used only by that proof. The private abbreviation
`finiteFixedField` occupies lines 32–36 and the local instance
`finiteFixedFieldSeparableClosureAlgebra` lines 38–44. The header occupies
lines 1–5, the `noncomputable section` line 24, the namespace line 26 and
the `open` lines 28–30.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M272.011, `LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv` | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_abstractFixedFieldEquivStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring_eq_comap_abstractFixedFieldEquiv`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  Its explicit parameters become universal binders in the same order, and
  the proof is omitted for the separate proof phase.
- The private abbreviation `finiteFixedField K H` is unfolded to
  `abstractFixedField K (SeparableClosure K) H.field`, which is its body.
- The source's file-level local instance
  `finiteFixedFieldSeparableClosureAlgebra` is replaced by a `letI` with the
  same body, placed after the binder `H` and before the binder `e`, whose
  type is the first place that uses it.
- The source's `finiteExtensionSpectralNormedField`,
  `finiteExtensionSpectralValuativeRel` and
  `finiteExtensionSpectralIsNonarchimedeanLocalField` are replaced by the
  Library's `Langlands.LocalField.FiniteExtension.normedField`,
  `valuativeRel` and `isLocalField`, as explained above. The four `letI`
  lines on `F` and the conclusion are otherwise the source text.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the four Library modules listed in the
  table above (the `FiniteAbstractField`, `abstractFixedField_finiteDimensional`,
  `localSeparableValuationSubring` and `Langlands.LocalField.FiniteExtension`
  modules).
- Of the source `open` lines 28–30 only the namespace `ClassFormation` is
  kept, as `open ClassFormation`; the statement uses no other opened name.
  The `noncomputable section` and the `open … in` prefix used only by the
  proof are omitted. All other declarations of the source file are
  omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M272.011 statement target. Its proof and the
other rows of the source file are not part of this unit.
