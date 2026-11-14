# NYLL finiteness of the principal-unit quotient tower: statements

Worker 111 adapts M147.023–M147.026 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`
(file SHA-256
`cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`).
The readable pinned original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Unit | Original declaration in `CyclicCohomology` | Source lines (docstring through proof; statement) | Adapted declaration in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M147.023 | `integerUnitsModPrincipalUnitsAtLevel_finite_zero` | 458–466; 459–461 | `integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement` |
| M147.024 | `integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalField` | 468–478; 470–473 | `integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalFieldStatement` |
| M147.025 | `integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finite` | 480–500; 482–486 | `integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finiteStatement` |
| M147.026 | `integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField` | 502–518; 504–507 | `integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalFieldStatement` |

## Meaning

Write `𝒪_Kˣ/U_K^n` for
`Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel K n`,
the quotient of the units of the valuation ring of `K` by the `n`-th principal
units, and `U_K^n/U_K^(n+1)` for
`Langlands.NYLL.LocalFieldTheory.PrincipalUnitsSuccQuot K n`. Each
proposition is a `Finite` assertion about one of these types:

- M147.023: for every field with a valuation relation, `𝒪_Kˣ/U_K^0` is
  finite. No local-field assumption occurs.
- M147.024: for a nonarchimedean local field, `𝒪_Kˣ/U_K^1` is finite.
- M147.025: for every field with a valuation relation and every `n`, if
  `U_K^n/U_K^(n+1)` and `𝒪_Kˣ/U_K^n` are finite, then `𝒪_Kˣ/U_K^(n+1)` is
  finite. Both finiteness hypotheses are instance-implicit binders, exactly
  as in the source.
- M147.026: for a nonarchimedean local field and every `n`,
  `𝒪_Kˣ/U_K^n` is finite.

## Telescopes

The shared universe is `u`, declared by the source at line 22 (`universe u`). The source
section has no `variable` command; every binder below is the theorem's own,
in source order and with source binder kinds:

```lean
integerUnitsModPrincipalUnitsAtLevel_finite_zeroStatement
    (K : Type u) [Field K] [ValuativeRel K] : Prop

integerUnitsModPrincipalUnitsAtLevel_finite_one_of_isNonarchimedeanLocalFieldStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Prop

integerUnitsModPrincipalUnitsAtLevel_finite_succ_of_finiteStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    [Finite (PrincipalUnitsSuccQuot K n)]
    [Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)] : Prop

integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalFieldStatement
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) : Prop
```

The bodies are, respectively, `Finite (IntegerUnitsModPrincipalUnitsAtLevel K 0)`,
`Finite (IntegerUnitsModPrincipalUnitsAtLevel K 1)`,
`Finite (IntegerUnitsModPrincipalUnitsAtLevel K (n + 1))` and
`Finite (IntegerUnitsModPrincipalUnitsAtLevel K n)`, copied verbatim from the
source targets.

## Reused declarations

- `Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel`
  (M146.001), imported from
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions`,
  the namespaced adaptation of the source's
  `CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel`.
- `Langlands.NYLL.LocalFieldTheory.PrincipalUnitsSuccQuot` (M132.001),
  imported from
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions`,
  the namespaced adaptation of the source's `LocalFieldTheory.PrincipalUnitsSuccQuot`.
  The source's `open LocalFieldTheory` (line 18) becomes
  `open Langlands.NYLL.LocalFieldTheory`, so the name is written unqualified
  exactly as in the source.
- Mathlib's `IsNonarchimedeanLocalField`, from
  `Mathlib.NumberTheory.LocalField.Basic`.

## Modifications

- The namespace `CyclicCohomology` becomes `Langlands.NYLL.CyclicCohomology`.
- Each theorem becomes a `Prop`-valued `def` with the suffix `Statement`
  whose body is exactly the source target; the source proofs (which use
  `principalUnits_zero`, the residue-unit equivalence, the successor exact
  sequence and `finite_principalUnitsSuccQuot`) are not ported here. Proofs
  of these targets are separate `lean.proof@1` work.
- The four NYLL imports of the source module are replaced by the two
  published Library modules above and Mathlib's local-field module, which
  supply every constant the targets mention. The source's
  `noncomputable section`, `universe u` and `open scoped ValuativeRel` are
  retained; the scoped notation is not used by the four targets.
- All other declarations of the source module are omitted; none of them
  appears in these four targets.
- Docstrings are rewritten to describe the proposition and name the unit.

No hypothesis is added or removed, no proof is supplied and no instance is
declared. The copyright and author header is retained, followed by a
modification notice. The Apache-2.0 `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` in the Library remain applicable. These statements
prove no class-formation or reciprocity theorem.
