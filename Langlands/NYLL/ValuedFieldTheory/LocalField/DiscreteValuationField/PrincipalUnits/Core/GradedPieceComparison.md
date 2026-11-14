# NYLL M231.033: concrete and abstract principal-unit graded pieces

This module adapts one data unit of Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` (NYLL). For a complete discrete valuation
field and a level `n`, it identifies the concrete adjacent quotient
`U^n/U^(n+1)` of the principal-unit filtration with the graded piece of the same
filtration viewed through the abstract antitone-filtration API.

## Declaration and parameters

`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitSuccQuotEquivGradedPiece`
takes the implicit field `{K : Type u}` with `[Field K]`, the explicit shared
`(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K)`
and the explicit `(n : ℕ)`. The universes `u` and `v` are independent level
parameters. No positivity hypothesis on `n` and no finiteness hypothesis on the
residue field are assumed.

It returns a multiplicative equivalence (data, not a proposition)

`principalUnitSuccQuot F n ≃* (toPrincipalUnitFiltration F).principalUnitGradedPiece n`,

both sides being types in `Type u`. Here:

- `principalUnitSuccQuot F n` (NYLL M231.023, published in
  `PrincipalUnits.Core.SuccessorQuotient`) is the quotient
  `higherPrincipalUnitGroup F n ⧸ (higherPrincipalUnitGroup F (n+1)).subgroupOf
  (higherPrincipalUnitGroup F n)`, with its canonical commutative group
  structure (M231.024).
- `toPrincipalUnitFiltration F` (NYLL M231.020, published in
  `PrincipalUnits.Core.Filtration`) is the concrete principal-unit filtration
  `n ↦ higherPrincipalUnitGroup F n` of `F.valuationSubringˣ`, packaged as an
  `AntitoneSubgroupFiltration`.
- `principalUnitGradedPiece` (published in `Units.GradedPiece`) is the abstract
  graded piece `U.principalUnitSubquotient n (n + 1)` of a filtration `U`. Its
  group structure and the equivalence below need normality of the level-`(n+1)`
  subgroup; Lean infers it because the unit group `F.valuationSubringˣ` is
  commutative.

The equivalence is the composite

`principalUnitSuccQuotConcreteEquiv F n` followed by the inverse of
(`principalUnitGradedPieceEquivSubquotient (toPrincipalUnitFiltration F) n`
then `principalUnitSubquotientConcreteEquiv (toPrincipalUnitFiltration F) n (n + 1)`).

The first maps the successor quotient to its concrete quotient. The other two
map the abstract graded piece first to the abstract subquotient at levels
`n, n + 1` and then to the concrete quotient
`U.principalUnitSubgroup n ⧸ (U.principalUnitSubgroup (n+1)).subgroupOf
(U.principalUnitSubgroup n)`. For `U = toPrincipalUnitFiltration F` that
quotient is definitionally the concrete quotient above. Each of the three is
defined as `MulEquiv.refl`, so the composite sends a class to the same class.

## Source

Naganori Yamaguchi (assisted by OpenAI Codex), `n-yamaguchi-0729/ClassFieldTheory`,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`
(file SHA-256
`415353484b021d45b0a0d02fe3d57049ec1c92dc8ca8da27477e403b0d1f0604`).
The Lean source is in registered source `external-lean-reuse-snapshots-2026-10-21`
(fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); its
attribution and notice files are in `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The unit
number is that of the public NYLL port partition,
`notes/reuse/nyll-public-port/m217-m240.md`.

M231.033 is the declaration at source line 540: its docstring is lines 538–539
and its type and body are lines 540–547. The source context consists of the
namespaces `LocalFieldTheory`, `DiscreteValuationField`, `CompleteDVF` and
`higherPrincipalUnitGroup` (lines 21, 31, 32 and 36), `noncomputable section`
(line 25, inside `LocalFieldTheory`), `universe u v` (line 29),
`variable {K : Type u} [Field K]` (line 34) and
`variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)`
(line 40).

## Modifications

- Every namespace is prefixed by `Langlands.NYLL`. The declaration is placed
  directly in the single combined namespace instead of the source's four nested
  namespace commands, and the field-package type in the `F` variable is written
  with its full published name
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
- The module contains only this unit. Its imports are the three published
  modules that supply its ingredients:
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.SuccessorQuotient`
  (M231.023–026),
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core.Filtration`
  (M231.020) and
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.GradedPiece`
  (the abstract graded piece and its equivalence with the subquotient, which
  imports the abstract subquotient module). They replace the source file's
  seven imports (lines 7–13).
- The source commands `open ValuationTheory`, `open scoped BigOperators` and
  `open ValuationTheory.DiscreteValuationField.DVF` are omitted; this
  declaration does not use them.
- The `noncomputable section` and `universe u v` commands are placed before the
  combined namespace rather than inside `LocalFieldTheory`, and the section is
  closed explicitly at the end of the file. A modification note in the license
  header and a module docstring are added.

The declaration name, binders, universe levels, docstring, result type and body
are copied unchanged from the source: lines 34–43 of
`GradedPieceComparison.lean` are byte-identical to source lines 538–547. The
qualified references such as `higherPrincipalUnitGroup.principalUnitSuccQuot`
and `AntitoneSubgroupFiltration.principalUnitGradedPieceEquivSubquotient`
resolve, from inside the prefixed namespace, to the published `Langlands.NYLL`
declarations.

The intervening source units M231.027–032 (theorems, a lift and a finiteness
instance) are not used by this definition and are not ported here.

The original copyright and author header is retained. The Apache-2.0 license
and attribution are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 299 prepared the draft; Worker 479 restored the verbatim source
docstring and spelling and wrote this description.
