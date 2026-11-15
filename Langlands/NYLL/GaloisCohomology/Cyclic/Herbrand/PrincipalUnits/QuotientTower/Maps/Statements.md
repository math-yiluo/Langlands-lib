# NYLL M147.002, M147.004, M147.011–.013: targets for the level-change maps of the principal-unit quotient tower

The paired Lean file adapts the statements of five theorems of Naganori
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

| Unit | Source theorem after `CyclicCohomology.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.CyclicCohomology.` |
| --- | --- | --- | --- | --- | --- |
| M147.002 | `integerUnitsModPrincipalUnitsMapOfLe_mk` | 39 | 41–46 | 47–48 | `integerUnitsModPrincipalUnitsMapOfLe_mkStatement` |
| M147.004 | `integerUnitsModPrincipalUnitsSuccMap_mk` | 57 | 59–64 | 65 | `integerUnitsModPrincipalUnitsSuccMap_mkStatement` |
| M147.011 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk` | 178 | 180–185 | 186–188 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement` |
| M147.012 | `integerUnitsSuccMap_comp_principalUnitsSuccQuot` | 190 | 191–194 | 194–209 | `integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement` |
| M147.013 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker` | 211–212 | 213–216 | 216–238 | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement` |

The source theorems M147.002, M147.004 and M147.011 carry `@[simp]` (lines
40, 58 and 179).

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

The statements use the three maps M147.001
`integerUnitsModPrincipalUnitsMapOfLe`, M147.003
`integerUnitsModPrincipalUnitsSuccMap` and M147.010
`principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc`, ported in the
companion module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Definitions`
of this contribution. The published NYLL declarations used are, in
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
resolves to `Langlands.NYLL.LocalFieldTheory`. They also use Mathlib's
`MonoidHom.comp`, the identity `1` of the monoid of homomorphisms,
`MonoidHom.range` and `MonoidHom.ker`.

## Targets and complete telescopes

### M147.002

```lean
/-- Target: the level-change map sends a unit class to the class of the same
unit. -/
def integerUnitsModPrincipalUnitsMapOfLe_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) : Prop :=
    integerUnitsModPrincipalUnitsMapOfLe K hnm
        (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x
```

For `n ≤ m` and a unit `x` of `𝒪_K`, the level-change map sends the class of
`x` modulo `U_K^m` to the class of `x` modulo `U_K^n`.

### M147.004

```lean
/-- Target: the successor-level map sends a unit representative to its
successor quotient class. -/
def integerUnitsModPrincipalUnitsSuccMap_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) : Prop :=
    integerUnitsModPrincipalUnitsSuccMap K n
        (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
      integerUnitsModPrincipalUnitsAtLevelMk K n x
```

The successive projection sends the class of `x` modulo `U_K^(n+1)` to the
class of `x` modulo `U_K^n`.

### M147.011

```lean
/-- Target: the principal-unit quotient map sends a representative to its
integer-unit class. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) : Prop :=
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
        (principalUnitsSuccQuotMk K n u) =
      integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ)
```

For `u ∈ U_K^n`, the map `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1)` sends the class
of `u` to the class of `u`, viewed as a unit of `𝒪_K`.

### M147.012

```lean
/-- Target: the principal-unit inclusion followed by the successor map is the
canonical quotient map. -/
def integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Prop :=
    (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1
```

The composite `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n` is the
trivial homomorphism `1`. (The wording of the source docstring, kept after the
`Target:` prefix, describes the two maps rather than this conclusion.)

### M147.013

```lean
/-- Target: exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
def principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Prop :=
    MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
      MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n)
```

The sequence `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n` is exact in the
middle: the range of the first map is the kernel of the second.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.CyclicCohomology`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proofs are omitted:
   this contribution publishes the proposition targets, and their proofs
   are separate work.
3. Omit the `@[simp]` attributes of M147.002, M147.004 and M147.011: a
   definition of a proposition is not a simp lemma.
4. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
5. Replace the four source imports by the companion module
   `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Definitions`,
   which imports the published modules of the names listed above.
6. Keep the namespace, the open, the noncomputable section, the universe
   declaration and the scoped open; omit the three definitions (ported in the
   companion module) and the other declarations of the source file.
7. No helper declaration, instance or linter option is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host Herbrand-quotient, class-formation, Tate or
reciprocity target.

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
