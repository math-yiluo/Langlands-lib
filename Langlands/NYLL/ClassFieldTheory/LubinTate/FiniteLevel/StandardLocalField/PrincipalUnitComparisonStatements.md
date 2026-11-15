# Standard local field: principal-unit comparison targets (M335.014, M335.017)

This module states, and does not prove, the two principal-unit image
comparisons for the canonical local-field package of a topology-first
nonarchimedean local field. Both are Prop-valued definitions.

## Declarations

Throughout, `K : Type` carries `[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`, and `n : ℕ` is explicit. `K` is explicit, as in
the source section variable `(K : Type)`.

- `Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnitsStatement K n`
  (M335.014) asserts

  ```
  (higherPrincipalUnitGroup (standardLocalField K).toCompleteDVF n).map
      (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom =
    principalUnits K n
  ```

  The image of the `n`-th higher principal-unit subgroup of the packaged
  valuation ring of `standardLocalField K`, under the inverse of the canonical
  integer-unit equivalence `𝒪[K]ˣ ≃* (standardLocalField K).valuationSubringˣ`,
  is the topology-first subgroup `{u ∈ 𝒪[K]ˣ | u - 1 ∈ 𝓂[K]^n}`.

- `Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnitsStatement K n`
  (M335.017) asserts

  ```
  (higherPrincipalUnitGroup (standardLocalField K).toCompleteDVF n).map
      (standardLocalFieldValuationUnitsToFieldUnits K) =
    Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n
  ```

  The image of the same subgroup in `Kˣ`, under the packaged valuation-unit
  inclusion, is the topology-first field principal-unit subgroup, namely the
  image of `principalUnits K n` in `Kˣ`.

## Declarations used

All are consumed by published Lean name:

| Name in the statements | Declaration | Source unit |
|---|---|---|
| `standardLocalField` | `Langlands.NYLL.LubinTate.standardLocalField` | M335.001 |
| `standardLocalFieldIntegerUnitsEquiv` | `Langlands.NYLL.LubinTate.standardLocalFieldIntegerUnitsEquiv` | M335.011 |
| `standardLocalFieldValuationUnitsToFieldUnits` | `Langlands.NYLL.LubinTate.standardLocalFieldValuationUnitsToFieldUnits` | M335.015 |
| `higherPrincipalUnitGroup` | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup` | M225.001 |
| `principalUnits` | `Langlands.NYLL.LocalFieldTheory.principalUnits` | NYLL `PrincipalUnits.lean` |
| `fieldPrincipalUnits` | `Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits` | NYLL `StandardOpenSubgroups.lean` |

`(standardLocalField K).toCompleteDVF` is the generated parent projection of
the shared FM package `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`;
`(standardLocalField K).valuationSubring` is that package's abbreviation for
`(standardLocalField K).toCompleteDVF.valuationSubring`, so the map domain and
the subgroup's ambient group agree by reducible unfolding, as in the source.

## Source correspondence

Original: Naganori Yamaguchi, NYLL ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`,
SHA-256 `88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Target | Source theorem | Source lines (statement) |
|---|---|---|
| `…_map_eq_principalUnitsStatement` | `LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits` | 204–209 (proof 210–227 omitted) |
| `…_map_eq_fieldPrincipalUnitsStatement` | `LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnits` | 248–253 (proof 254–261 omitted) |

The section context is source lines 26–38: `noncomputable section`,
`open scoped ValuativeRel`, `namespace LubinTate`, the opens of
`LocalFieldTheory`, `LocalFieldTheory.DiscreteValuationField` and
`LocalFieldTheory.DiscreteValuationField.CompleteDVF`, and
`variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]`. The asserted equalities are copied verbatim
from the source statements; the subgroup, maps and right-hand sides are the
source's own declarations under the `Langlands.NYLL` prefix.

## Modifications

- Extraction: only the statements of M335.014 and M335.017; their proofs and all
  other units of the source file are omitted. No proof is included.
- Each source `theorem` became a `def … : Prop` named with the suffix `Statement`.
- Namespace: `LubinTate` became `Langlands.NYLL.LubinTate`; the source opens are
  resolved relative to it, so they name `Langlands.NYLL.LocalFieldTheory…`.
- The source open of `LocalFieldTheory.IsNonarchimedeanLocalField` is omitted
  because neither statement uses a declaration from that namespace.
- Imports: the six source imports (whole `DiscreteValuationField.Basic`,
  `PrincipalUnits.ResidueQuotient`, `PrincipalUnits.TeichmullerDecomposition`,
  `FiniteExtensionCompleteDVF`, `IdealQuotients`, `StandardOpenSubgroups`
  modules) are replaced by four focused imports of the published modules
  providing the declarations listed above:
  - `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerUnitsEquiv`
    (`standardLocalFieldIntegerUnitsEquiv`; through it `standardLocalField` and
    the shared FM `LocalField` package);
  - `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationUnitsToFieldUnits`
    (`standardLocalFieldValuationUnitsToFieldUnits`);
  - `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`
    (`higherPrincipalUnitGroup`);
  - `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Definitions`
    (`fieldPrincipalUnits`; through it `principalUnits`).

  No residue-quotient, Teichmüller, ideal-quotient or maximal-ideal-transport
  (M335.008–.010, .013) result is needed to state the targets.
- Module documentation replaced; the original copyright, Apache-2.0 and author
  lines are retained, followed by a modification notice.
- No universe, parameter, hypothesis, instance or mathematical type was changed.
  The source environment was Lean 4.35.0-rc2; the approved environment is
  Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  M335 has no patch10 change.

## Licence

The source is released under Apache-2.0. `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are retained unmodified.
