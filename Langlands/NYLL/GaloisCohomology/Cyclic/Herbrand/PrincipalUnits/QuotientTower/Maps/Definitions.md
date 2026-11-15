# NYLL M147.001, M147.003, M147.010: level-change maps of the principal-unit quotient tower

The paired Lean file adapts three definitions of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`.
The pinned source file has SHA-256
`cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `CyclicCohomology.` | Docstring | Header | Body | Adapted name after `Langlands.NYLL.CyclicCohomology.` |
| --- | --- | --- | --- | --- | --- |
| M147.001 | `integerUnitsModPrincipalUnitsMapOfLe` | 26 | 27–30 | 31–37 | `integerUnitsModPrincipalUnitsMapOfLe` |
| M147.003 | `integerUnitsModPrincipalUnitsSuccMap` | 50 | 51–54 | 55 | `integerUnitsModPrincipalUnitsSuccMap` |
| M147.010 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc` | 163–164 | 165–168 | 169–176 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc` |

The source imports
`Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core`,
`Nyll.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps`,
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing`
and
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients`
(lines 7–10). The source context, kept verbatim, is
`namespace CyclicCohomology` (line 16), `open LocalFieldTheory` (line 18),
`noncomputable section` (line 20), `universe u` (line 22),
`open scoped ValuativeRel` (line 24) and the closing lines 748–749. The
source file has no `variable` command: every declaration binds its own
field `K` and its instances `[Field K] [ValuativeRel K]`, so the telescopes
shown below are complete.

The other declarations of the source file are not part of this module. The
statements of the theorems M147.002, M147.004, M147.011, M147.012 and
M147.013 are in the companion module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
of this contribution.

The published NYLL declarations used are, in
`Langlands.NYLL.CyclicCohomology`, the quotient `IntegerUnitsModPrincipalUnitsAtLevel K n`
of the integer units `𝒪[K]ˣ` by the level-`n` principal units (M146.001),
its commutative-group instance `integerUnitsModPrincipalUnitsAtLevelCommGroup`
(M146.002), the class map `integerUnitsModPrincipalUnitsAtLevelMk` (M146.004)
and the lift `integerUnitsModPrincipalUnitsAtLevelLift` (M146.008), all in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions`; and, in `Langlands.NYLL.LocalFieldTheory`, the
principal-unit subgroups `principalUnits K n` (M131.001, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`) and the successor quotient
`PrincipalUnitsSuccQuot K n`, the quotient of `principalUnits K n` by
`(principalUnits K (n + 1)).subgroupOf (principalUnits K n)` (M132.001), with its
instance `principalUnitsSuccQuotCommGroup` (M132.002), its class map
`principalUnitsSuccQuotMk` (M132.004) and its lift
`principalUnitsSuccQuotLift` (M132.005), all in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions`. The
`LocalFieldTheory` names are found through the source line
`open LocalFieldTheory`, which inside `Langlands.NYLL.CyclicCohomology`
resolves to `Langlands.NYLL.LocalFieldTheory`. The embedded proofs also use the published theorems
`integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` (M146.010, in
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U010.Proofs`; its type is the published target
`integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement K n x`, the
proposition `integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔ x ∈ principalUnits K n`
of `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Statements`) and
`Langlands.NYLL.LocalFieldTheory.principalUnits_antitone` (M131.005, in
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.U005.Proofs`), and Mathlib's `MonoidHom`,
`MonoidHom.comp`, `Subgroup.subtype`, `MonoidHom.mem_ker`,
`MonoidHom.comp_apply` and `Nat.le_succ`.

## Definitions

### M147.001

```lean
/-- The natural projection `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` for `n ≤ m`. -/
def integerUnitsModPrincipalUnitsMapOfLe
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m) :
    IntegerUnitsModPrincipalUnitsAtLevel K m →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsAtLevelLift m
    (integerUnitsModPrincipalUnitsAtLevelMk K n)
    (by
      intro x hx
      have hmk : ∀ y : 𝒪[K]ˣ,
          integerUnitsModPrincipalUnitsAtLevelMk K n y = 1 ↔ y ∈ principalUnits K n :=
        fun y => integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n y
      rw [MonoidHom.mem_ker,
        hmk]
      exact principalUnits_antitone K hnm hx)
```

For `n ≤ m`, the map `𝒪_Kˣ/U_K^m → 𝒪_Kˣ/U_K^n` is the lift of the class map
at level `n` through the quotient at level `m`. The tactic block proves that
every `x ∈ U_K^m` lies in the kernel of the class map at level `n`, that is,
in `U_K^n`, by the antitonicity of the filtration.

### M147.003

```lean
/-- The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`. -/
def integerUnitsModPrincipalUnitsSuccMap
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) →*
      IntegerUnitsModPrincipalUnitsAtLevel K n :=
  integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)
```

The successive projection `𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n` is M147.001 for
`n ≤ n + 1`.

### M147.010

```lean
/-- The graded quotient `U_K^n/U_K^(n+1)` as the kernel source inside
`𝒪_Kˣ/U_K^(n+1)`. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    PrincipalUnitsSuccQuot K n →*
      IntegerUnitsModPrincipalUnitsAtLevel K (n + 1) :=
  principalUnitsSuccQuotLift n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype)
    (by
      intro u hu
      have hmk : ∀ y : 𝒪[K]ˣ,
          integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) y = 1 ↔
            y ∈ principalUnits K (n + 1) :=
        fun y => integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K (n + 1) y
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        hmk]
      exact hu)
```

The map `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1)` is the lift through the successor
quotient of the composite of the inclusion `U_K^n → 𝒪_Kˣ` with the class map
at level `n + 1`. The tactic block proves that every `u ∈ U_K^(n+1)` (viewed
in `U_K^n`) lies in the kernel of that composite.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definitions lie in
   `Langlands.NYLL.CyclicCohomology`.
2. In the proof terms of M147.001 and M147.010 (the third argument of
   `integerUnitsModPrincipalUnitsAtLevelLift` and of
   `principalUnitsSuccQuotLift`, each a proof that a subgroup lies in a
   kernel), the source rewrites with
   `rw [MonoidHom.mem_ker, integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]`
   and `rw [MonoidHom.mem_ker, MonoidHom.comp_apply, integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]`.
   The published theorem `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`
   has the Prop-valued type
   `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement K n x`, which
   `rw` does not unfold. Each proof therefore first states the equivalence at
   the level used (`n` for M147.001, `n + 1` for M147.010) for every
   `y : 𝒪[K]ˣ` as a local hypothesis `hmk`, proved by that theorem, and
   rewrites with `hmk` in its place. The rest of each tactic block is
   unchanged. The change is inside a proof of a proposition, so the maps are
   those of the source.
3. Copy the docstrings, the binders and the rest of the bodies verbatim, with
   the source line breaks.
4. Replace the four source imports by the four focused published modules
   `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions`, `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U010.Proofs`,
   `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.U005.Proofs` and
   `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.SuccessorDefinitions`, and the source module
   docstring by a description of this module with a modification notice.
5. Keep the namespace, the open, the noncomputable section, the universe
   declaration and the scoped open; omit the other declarations of the
   source file.
6. No helper declaration, instance or linter option is added.

These are definitions only. They discharge no host Herbrand-quotient,
class-formation, Tate or reciprocity target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
