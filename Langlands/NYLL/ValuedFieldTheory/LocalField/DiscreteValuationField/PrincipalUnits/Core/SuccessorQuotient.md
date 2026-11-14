# NYLL M231.023–026: the concrete adjacent principal-unit quotient

This module adapts four consecutive data units of Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory` (NYLL). For a complete discrete valuation
field and a level `n`, they give the adjacent quotient `U^n/U^(n+1)` of the
concrete principal-unit filtration, its group structure, its identification with
the concrete quotient that implements it, and the quotient homomorphism.

## Declarations and parameters

All four declarations lie in the namespace
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`.
Each takes the implicit field `{K : Type u}` with `[Field K]`, the explicit shared
`(F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u,v} K)`
and the explicit `(n : ℕ)`. The universes `u` and `v` are independent level
parameters of every declaration. No positivity hypothesis on `n` and no finiteness
hypothesis on the residue field are assumed.

Write `U^n` for `higherPrincipalUnitGroup F n`, the published subgroup of
`F.valuationSubringˣ` whose elements `u` satisfy
`(u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n`
(module `PrincipalUnits.Filtration.Definitions`). Write `Q n` for the concrete
quotient `U^n ⧸ (U^(n+1)).subgroupOf U^n`, the quotient of the group `U^n` by
the subgroup of `U^n` whose elements lie in `U^(n+1)`.

| Unit | Short name | Kind | Lean type |
| --- | --- | --- | --- |
| M231.023 | `principalUnitSuccQuot` | `def` | `Type u`, defined as `Q n` |
| M231.024 | `principalUnitSuccQuotCommGroup` | `instance` | `CommGroup (principalUnitSuccQuot F n)` |
| M231.025 | `principalUnitSuccQuotConcreteEquiv` | `def` | `principalUnitSuccQuot F n ≃* Q n` |
| M231.026 | `principalUnitSuccQuotMk` | `def` | `U^n →* principalUnitSuccQuot F n` |

- `principalUnitSuccQuot F n` is the actual quotient type `Q n`, valued in `Type u`.
- `principalUnitSuccQuotCommGroup F n` unfolds the definition and supplies
  Mathlib's canonical commutative group structure on `Q n`: the quotient of the
  commutative group `U^n` by a subgroup, which is normal because `U^n` is commutative.
  It adds no competing instance on `Q n` itself.
- `principalUnitSuccQuotConcreteEquiv F n` is `MulEquiv.refl` on `Q n`,
  viewed through the definitional unfolding of `principalUnitSuccQuot F n`.
- `principalUnitSuccQuotMk F n` is `QuotientGroup.mk'` for the subgroup
  `(U^(n+1)).subgroupOf U^n`, viewed as a homomorphism into
  `principalUnitSuccQuot F n`.

All four are data (types, an instance, an equivalence and a homomorphism), not
propositions. Finiteness of the quotient, its cardinality, comparison maps with
the residue field and evaluation theorems such as the source's
`principalUnitSuccQuotConcreteEquiv_mk` (M231.027) are separate units and not
part of this module.

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
numbers are those of the public NYLL port partition, `notes/reuse/nyll-public-port/m217-m240.md`.

| Unit | Source declaration line | Source docstring and body lines |
| --- | --- | --- |
| M231.023 `principalUnitSuccQuot` | 418 | docstring 416–417, body 418–420 |
| M231.024 `principalUnitSuccQuotCommGroup` | 426 | docstring 422–425, body 426–432 |
| M231.025 `principalUnitSuccQuotConcreteEquiv` | 436 | docstring 434–435, body 436–448 |
| M231.026 `principalUnitSuccQuotMk` | 451 | docstring 450, body 451–459 |

The source section heading is line 414. The source context consists of the
namespaces `LocalFieldTheory`, `DiscreteValuationField`, `CompleteDVF` and
`higherPrincipalUnitGroup` (lines 21, 31, 32 and 36), `noncomputable section`
(line 25, inside `LocalFieldTheory`), `universe u v` (line 29),
`variable {K : Type u} [Field K]` (line 34) and
`variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)`
(line 40).

## Modifications

- Every namespace is prefixed by `Langlands.NYLL`. The four declarations are
  placed directly in the single combined namespace instead of the source's four
  nested namespace commands, and the field-package type in the `F` variable is
  written with its full published name
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
- The module contains only these four consecutive units. Its sole import is the
  published concrete subgroup module
  `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`,
  replacing the source file's seven imports (lines 7–13). These units need only
  the subgroup `higherPrincipalUnitGroup` and the Mathlib quotient-group API that
  this import already brings in.
- The source commands `open ValuationTheory`, `open scoped BigOperators` and
  `open ValuationTheory.DiscreteValuationField.DVF` are omitted; these
  declarations do not use them.
- The `noncomputable section` and `universe u v` commands are placed before the
  combined namespace rather than inside `LocalFieldTheory`, and the section is
  closed explicitly at the end of the file. A modification note in the license
  header and a new module docstring are added.

The declaration names, binders, universe levels, docstrings, result types and
bodies (including the `change` tactics) are copied unchanged from the source:
lines 32–75 of `SuccessorQuotient.lean` are byte-identical to source lines 416–459.

The original copyright and author header is retained. The Apache-2.0 license
and attribution are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
Worker 299 prepared the four-declaration draft; Worker 478 restored the verbatim
source docstrings and result-type spelling and wrote this description.
