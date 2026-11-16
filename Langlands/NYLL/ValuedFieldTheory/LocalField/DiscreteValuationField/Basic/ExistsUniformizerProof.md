# A local-field package has a uniformizer (M334.008)

This module proves
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.exists_uniformizer`.
Its complete type is the already published closed proposition
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.exists_uniformizerStatement.{u, v}`.
The independent universe parameters are ordered `u v`.

Unfolding that proposition gives

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K),
  ∃ pi : F.valuationSubring, F.toCompleteDVF.valuation.IsUniformizer (pi : K)
```

Thus every supplied local-field package has a uniformizer in its own
valuation subring for its chosen valuation. The implicit field, its field
instance and the explicit package have exactly the source binder order
and kinds. The published `LocalField` package and target are unchanged.

## Implemented proof and dependencies

The complete proof is

```lean
  intro K _ F
  exact F.toCompleteDVF.exists_uniformizer
```

After introducing the telescope inside the closed proposition, this is
the original M334.008 proof term. It applies the published theorem
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.exists_uniformizer`
to the parent `F.toCompleteDVF`. That theorem proves
`CompleteDVF.exists_uniformizerStatement F.toCompleteDVF`, whose unfolding
is the desired existential. The abbreviation `LocalField.valuationSubring`
reduces to the valuation subring of this parent, so Lean accepts the term
by definitional equality. No transport or choice of a different valuation
is needed.

The two imports are:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.ExistsUniformizerStatement`,
  supplying the exact closed target and the published shared local-field
  definitions;
- `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.U022.Proofs`,
  supplying the now-published M107.022 theorem used by the source proof.

The current Library was searched before authoring. M107.022 is present in
the Library base `210249ebac6bad5d2928923e3aaa6ea517d31490`, so this module
reuses it as required by the task. The second import makes that published
theorem available. No M107 wrapper is created here.

The reused M107.022 implementation changes its existential to one over
`F.valuation.valuationSubring` and applies Mathlib's
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`. Its cyclic and
nontrivial value-group instances come from rank-one discreteness.
For the local-field package here,
`CompleteDVF.instCompleteDiscrete` stores completeness and rank-one
discreteness, and the published
`Valuation.IsCompleteDiscrete.isRankOneDiscrete` instance supplies
Mathlib's `IsRankOneDiscrete` instance. The predicate
`Valuation.IsUniformizer` uses this stored valuation and instance.
Residue-field finiteness and adic completeness remain in the package;
the uniformizer argument needs only rank-one discreteness.

The upstream M107.022 proof calls `F.toDVF.exists_uniformizer`
(M103.020). That source proof unfolds the valuation-subring abbreviation
and uses the same Mathlib theorem. The published M107.022 implementation
inlines that final step. This module depends on that accepted proof by
Lean name and retains the original M334.008 delegation.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, retained under
`n-yamaguchi-0729--ClassFieldTheory/source/` in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content SHA-256
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content SHA-256
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The project literature errata index has no entry for this source.

| Source unit | Original passage | Correspondence |
| --- | --- | --- |
| M334.008 | `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`, lines 73–76 | Same theorem name, docstring, full scope and proof term, with the closed published target as its type. |
| M107.022 | `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`, lines 200–203 | The complete-DVF uniformizer theorem called by M334.008; reused from the Library. |
| M103.020 | `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Basic.lean`, lines 148–153 | The underlying DVF proof ending in Mathlib's uniformizer-existence theorem; implemented within the reused M107.022 proof. |

The three original files were read at the cited passages, and their
SHA-256 values were checked:

- Local-field `Basic.lean`:
  `69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`;
- valuation `Complete.lean`:
  `509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`;
- valuation `Basic.lean`:
  `abda99fd0b28655e1317ae832e8c94c7431b7229d99cf07138d89c4a5c953493`.

Worker 768 made these adaptations on 16 November 2026:

- extracted only M334.008 into the focused proof module;
- prefixed its namespace with `Langlands.NYLL`;
- stated the theorem with the exact published closed proposition as its
  type, introducing `{K : Type u} [Field K] (F : LocalField.{u, v} K)`
  inside the proof instead of as outer theorem binders;
- replaced the nine upstream imports by the two published modules above;
- retained independent universes `u v` in order and omitted unused `w x`
  and the unnecessary opened valuation namespace;
- retained the source proof term and declaration docstring, replaced the
  module documentation, added a modification note and wrote this Markdown.

No hypothesis, conclusion, structure, abbreviation, instance or imported
Library file is changed. No other source theorem is introduced.

The development `lean_check` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled this module with no errors
or warnings. Declaration inspection reported universe parameters `u v`
and only `propext`, `Classical.choice` and `Quot.sound` as axioms.
Independent review and exact-target validation are separate acceptance
requirements.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim. The unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in the Library.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No external repository is imported and no Mathlib source is copied.
