# Finiteness of the zeroth principal-unit quotient

This module proves
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevel_finite_zero`,
the proof phase of M147.023 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem integerUnitsModPrincipalUnitsAtLevel_finite_zero
    (K : Type u) [Field K] [ValuativeRel K] :
    integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement K
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance. No
topology, local-field or finiteness hypothesis is assumed. The target unfolds
to `Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0)`, finiteness of the
named quotient `𝒪[K]ˣ ⧸ principalUnits K 0` of valuation-ring units by the
zeroth principal units. No hypothesis is added.

## Implemented proof

```lean
  have h₀ : principalUnits K 0 = ⊤ := principalUnits_zero K
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [h₀]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv
```

1. The published theorem
   `Langlands.NYLL.LocalFieldTheory.principalUnits_zero`, of the closed type
   `PrincipalUnitsZeroStatement` (`∀ K [Field K] [ValuativeRel K],
   principalUnits K 0 = ⊤`), is specialized to `K` as the equation `h₀`:
   the zeroth principal-unit subgroup is all of `𝒪[K]ˣ`.
2. Rewriting with `h₀` turns the goal `Finite (𝒪[K]ˣ ⧸ principalUnits K 0)`
   into `Finite (𝒪[K]ˣ ⧸ ⊤)`. Instance search closes it with Mathlib's
   `Subgroup.finite_quotient_of_finiteIndex` and
   `Subgroup.instFiniteIndexTop` (the top subgroup has index `1`).
3. Mathlib's `Finite.of_equiv` transports finiteness along the inverse of
   the published `integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0 :
   IntegerUnitsModPrincipalUnitsAtLevel K 0 ≃* (𝒪[K]ˣ ⧸ principalUnits K 0)`,
   viewed as an equivalence of types. Its codomain
   `IntegerUnitsModPrincipalUnitsAtLevel K 0` is the target's type.

No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L458-L466):
the docstring at line 458 and the theorem at lines 459–466 (telescope and
conclusion at 459–461, tactics at 462–466); the task's unit range 459–469
ends before the next declaration at 470. The retained original file has
SHA-256 `cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`.
The source proof is

```lean
  let : Finite (𝒪[K]ˣ ⧸ principalUnits K 0) := by
    rw [principalUnits_zero]
    infer_instance
  exact Finite.of_equiv (𝒪[K]ˣ ⧸ principalUnits K 0)
    (integerUnitsModPrincipalUnitsAtLevelConcreteEquiv K 0).symm.toEquiv
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.integerUnitsModPrincipalUnitsAtLevel_finite_zero` | `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevel_finite_zero` |
| Its statement | `integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement K` |
| Used `LocalFieldTheory.principalUnits_zero` | Published `Langlands.NYLL.LocalFieldTheory.principalUnits_zero` |

Modifications by Worker 134 on 14 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; add the line `have h₀ : principalUnits K 0 = ⊤ :=
principalUnits_zero K` and rewrite with `h₀` instead of
`principalUnits_zero`, because the published `principalUnits_zero` has the
closed `Statement` type rather than the source's bare equation, and `rw`
needs an equation; replace the source imports by the two imports below;
omit the source `noncomputable section` and all other source declarations.
The name, docstring, telescope and the remaining tactics are unchanged. The
partition records no patch10 change to this module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.FinitenessStatements`
  supplies the target and, through
  `...PrincipalUnits.QuotientReps.Definitions`, the quotient
  `IntegerUnitsModPrincipalUnitsAtLevel`, its group structure and the
  equivalence `integerUnitsModPrincipalUnitsAtLevelConcreteEquiv`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Proofs`
  is the published proof module of `principalUnits_zero` (Worker 229).

Both modules and everything they import are left unchanged.

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright
2026 Naganori Yamaguchi, author "Naganori Yamaguchi (assisted by OpenAI
Codex)", released under Apache-2.0. The Lean file carries the dated
modification record. The retained original belongs to the registered source
`external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`). The
unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker
134 adapted this proof directly from the pinned original. The statement is
Worker 111's, used unchanged.

This module proves only the level-zero case; finiteness at level one over a
nonarchimedean local field (M147.024), the successor step (M147.025) and all
levels (M147.026) are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
