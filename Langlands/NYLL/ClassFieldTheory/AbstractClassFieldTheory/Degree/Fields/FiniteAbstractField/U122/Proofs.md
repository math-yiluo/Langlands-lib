# NYLL M010.122: extensionality of finite abstract fields

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eqStatement`
by the theorem
`Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eq`. The
theorem's type is exactly that proposition applied to its source parameters,
`eq_of_field_eqStatement K L h`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has the implicit group `G : Type u` with instances
`[Group G] [TopologicalSpace G]`, and, explicitly, two finite abstract fields
`K L : FiniteAbstractField G` and the hypothesis `h : K.field = L.field` that
their underlying closed subgroups agree. Like the statement, it has one
universe parameter `u`, the universe of `G`.

The published structure `FiniteAbstractField G` has two fields: the closed
subgroup `field : ClosedSubgroup G` and the proof
`finite : Finite ((baseField G).toSubgroup ⧸ extensionSubgroup (baseField G) field (le_baseField field))`,
which is a proposition. Unfolding the published proposition gives `K = L`.

## Implemented proof

The complete proof body is

```lean
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      cases h
      rfl
```

The two `cases` steps destructure `K` and `L` into their closed subgroups and
finiteness proofs, turning the hypothesis into `h : K = L` between closed
subgroups. `cases h` substitutes one subgroup for the other, leaving the
goal that `⟨K, hK⟩` equals `⟨K, hL⟩`, still stated through
`eq_of_field_eqStatement`. The two finiteness proofs `hK` and `hL` have the
same proposition as type, so they are definitionally equal by proof
irrelevance, and `rfl` closes the goal after unfolding the statement
definition to this equality.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring. No auxiliary
declaration, extra hypothesis or instance is introduced. The development
check reports no errors or warnings, the single universe parameter `u`, and
only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.FiniteAbstractField.eq_of_field_eqStatement`
  in Degree.Fields.FiniteAbstractField.Statements.
- The published structure `Langlands.NYLL.ClassFormation.FiniteAbstractField`
  (Degree.Fields.FiniteAbstractField.Definitions), whose constructor `mk` is
  used by `cases`, together with the definitions its `finite` field mentions
  (`baseField`, `extensionSubgroup`, `le_baseField`), reached through the
  Statements module's imports.
- Lean's core `cases` tactic and `rfl`, with definitional proof irrelevance.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean:1102–1111`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L1102-L1111).
Lines 1102–1103 are the docstring, 1104–1105 the signature and 1106–1111 the
proof, inside `namespace FiniteAbstractField` (line 1100). The enclosing
`namespace ClassFormation` (line 22) has `open CyclicCohomology` (24),
`noncomputable section` (28), `universe u` (30) and the section variables
`{G : Type u} [Group G] [TopologicalSpace G]` (46). The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m010)
places this proof at M010.122 (source unit lines 1104–1113). The whole-file
SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation.FiniteAbstractField` | Adapted in `Langlands.NYLL.ClassFormation.FiniteAbstractField` |
| --- | --- |
| Asserted type of `eq_of_field_eq` (M010.122) | Published `eq_of_field_eqStatement` in Degree.Fields.FiniteAbstractField.Statements |
| Proof `eq_of_field_eq` | This theorem of the same adapted name in Degree.Fields.FiniteAbstractField.U122.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, omits the unused
`open CyclicCohomology`, keeps the `noncomputable section`, `universe u`, the
section variables and the docstring, and states the theorem's type as the
published proposition applied to `K L h`. The proof is unchanged.

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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M010.122. The other M010 units and any host
class-formation, cup, transfer, Tate or reciprocity target are separate work.
