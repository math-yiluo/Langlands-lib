# NYLL M138.007: reduction commutes with the residue-field algebra map

This module proves the published Library proposition
`Langlands.NYLL.LocalFieldTheory.residueField_algebraMap_residueStatement`
by the theorem
`Langlands.NYLL.LocalFieldTheory.residueField_algebraMap_residue`. The
theorem's type is exactly that proposition applied to its source parameters,
`residueField_algebraMap_residueStatement K L x`.

Its sole direct import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.ResidueStatement`.
That published Lean/Markdown pair and its imported chain remain unchanged.

## Target and parameters

The theorem has the explicit types `K L : Type u` with instances
`[Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]`, the
instance
`[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`
and an explicit integer `x : 𝒪[K]`, in the order of the statement. Like the
statement, it has one universe parameter `u`.

Unfolding the published proposition gives

```lean
algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
  IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x)
```

where `𝒪[K]`, `𝒪[L]` are the integer subrings of the given valuations,
`𝓀[K]`, `𝓀[L]` are their residue fields, and the algebra maps are the
canonical Mathlib instances for a valuation extension.

## Implemented proof

The complete proof body is `rfl`. The integer-ring algebra map is Mathlib's
restriction of `algebraMap K L` to the integer subrings, and Mathlib defines
the residue-field algebra between these local rings by lifting that map
through the residue quotient. Applied to the residue class of `x`, the
left-hand side therefore reduces by definitional unfolding to the residue
class of `algebraMap 𝒪[K] 𝒪[L] x`, which is the right-hand side. The
elaborator also unfolds the statement definition when checking `rfl`.
Mathlib states the same equality, also by `rfl`, as
`Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap` and
`IsLocalRing.ResidueField.algebraMap_residue`; the proof here uses neither.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring and its `@[simp]`
attribute. The attribute is retained as in the source (precedent:
Degree.Fields.U016.Proofs). No auxiliary declaration, extra hypothesis or
instance is introduced. The development check reports no errors or warnings,
the single universe parameter `u`, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalFieldTheory.residueField_algebraMap_residueStatement`
  in ResidueExtension.ResidueStatement.
- Mathlib's canonical instances, reached through that module's imports
  `Mathlib.RingTheory.Valuation.Extension` and
  `Mathlib.Topology.Algebra.Valued.ValuativeRel`: the integer-ring algebra
  of a valuation extension and the residue-field algebra between local
  rings, used only through their definitional unfolding.
- Lean's `rfl`.

No other NYLL or project proof is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean:88–96`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean#L88-L96).
Line 88 is the docstring, line 89 the `@[simp]` attribute, lines 90–95 the
signature and line 96 the proof `rfl`. The enclosing
`namespace LocalFieldTheory` (line 26) has `noncomputable section` (28),
`universe u` (30) and `open scoped ValuativeRel` (32). The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m121-m144.md#m138)
places this theorem at M138.007 (source start line 90). The whole-file
SHA-256 is
`09a3886306e3d31336cebf5df8f2384b06c3f33afd045b4492568f31d3a6bc06`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalFieldTheory` | Adapted in `Langlands.NYLL.LocalFieldTheory` |
| --- | --- |
| Asserted type of `residueField_algebraMap_residue` (M138.007) | Published `residueField_algebraMap_residueStatement` in ResidueExtension.ResidueStatement |
| Proof `residueField_algebraMap_residue` | This theorem of the same adapted name in ResidueExtension.U007.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published ResidueStatement import, keeps the
`noncomputable section`, `universe u`, `open scoped ValuativeRel`, the
docstring and `@[simp]`, and states the theorem's type as the published
proposition applied to `K L x`. The proof is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M138.007. The other M138 units, including M138.026,
are separate work.
