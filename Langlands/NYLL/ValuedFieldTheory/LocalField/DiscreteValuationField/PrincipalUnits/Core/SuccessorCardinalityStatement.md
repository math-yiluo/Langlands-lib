# Cardinality of a positive principal-unit graded piece

This file states NYLL M231.063 as the proposition
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.card_principalUnitSuccQuot_eq_residue_of_uniformizerStatement`.
Its parameters are, in this order: an implicit field `K : Type u` with
`[Field K]`, an explicit `F : CompleteDVF.{u,v} K`, an instance
`[Finite F.residueField]`, an implicit `pi : F.valuationSubring`, an
explicit proof `hpi : F.valuation.IsUniformizer (pi : K)`, a natural number
`n` and an explicit proof `hn : 1 ≤ n`. The proposition says that
`Nat.card (principalUnitSuccQuot F n) = Nat.card F.residueField`, where
`principalUnitSuccQuot F n` is the concrete quotient `U^n/U^(n+1)` of
`higherPrincipalUnitGroup F n` by `higherPrincipalUnitGroup F (n+1)`
(M231.023, module `PrincipalUnits.Core.SuccessorQuotient`). The declaration
is a `def` returning `Prop`; the universes `u` and `v` are independent. The
conclusion does not mention `pi`, `hpi` or `hn`; they are kept so that the
telescope is the source's.

## Source

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`:
theorem `card_principalUnitSuccQuot_eq_residue_of_uniformizer` (M231.063),
docstring lines 1142–1143, signature and conclusion lines 1144–1149, proof
lines 1150–1161. The binders `{K : Type u} [Field K]` and
`(F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)` come
from the section variables at lines 34 and 40; no other section variable
or section boundary intervenes. The pinned file is in the registered
snapshot `external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory`, file SHA-256
`415353484b021d45b0a0d02fe3d57049ec1c92dc8ca8da27477e403b0d1f0604`). The
Apache-2.0 attribution and notice files retained as `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` come from the registered supplement
`nyll-classfieldtheory-fbd320cd-supplement`.

## Modifications

- The namespaces `LocalFieldTheory` and `ValuationTheory` are prefixed with
  `Langlands.NYLL`; `higherPrincipalUnitGroup.principalUnitSuccQuot F n`
  is written `principalUnitSuccQuot F n`, which resolves to the same
  declaration inside the `higherPrincipalUnitGroup` namespace.
- The source theorem becomes a `def` with suffix `Statement` returning its
  exact proposition; the proof is omitted and is separate work.
- The section variables are written directly as binders of the `def`,
  with the same binder kinds (`K` implicit, `F` explicit).
- The docstring is shortened and tagged with the unit ID M231.063.
- `set_option linter.unusedVariables false in` silences the unused-variable
  linter for this declaration so that the source binder names `hpi` and `hn`
  are kept.
- The only import is the concrete successor-quotient data module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SuccessorQuotient`,
  whose subgroup dependency supplies `CompleteDVF`, its valuation subring,
  valuation and residue field. The source's other imports and opens are
  not used by the statement.

No hypothesis is added or removed. The original attribution and the
Apache-2.0 license are retained in the Lean header and in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
