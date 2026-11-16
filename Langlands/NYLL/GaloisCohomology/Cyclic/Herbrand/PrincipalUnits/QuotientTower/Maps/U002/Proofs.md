# The level-change map on a unit class

This module proves
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe_mk`,
the proof phase of M147.002 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe_mkStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem integerUnitsModPrincipalUnitsMapOfLe_mk
    (K : Type u) [Field K] [ValuativeRel K] {n m : Nat} (hnm : n ≤ m)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMapOfLe_mkStatement K hnm x
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance, levels
`n ≤ m` (with `n`, `m` implicit) and a unit `x` of the valuation ring
`𝒪[K]`. The target unfolds to

```lean
integerUnitsModPrincipalUnitsMapOfLe K hnm
    (integerUnitsModPrincipalUnitsAtLevelMk K m x) =
  integerUnitsModPrincipalUnitsAtLevelMk K n x
```

that is, the projection `𝒪[K]ˣ/U_K^m → 𝒪[K]ˣ/U_K^n` sends the class of `x`
at level `m` to the class of `x` at level `n`. No hypothesis is added.

## Implemented proof

```lean
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x
```

The published definition `integerUnitsModPrincipalUnitsMapOfLe K hnm` (M147.001,
module `...QuotientTower.Maps.Definitions`) is the quotient lift
`integerUnitsModPrincipalUnitsAtLevelLift m (integerUnitsModPrincipalUnitsAtLevelMk K n) h₀`
of the level-`n` class map, where `h₀` is its embedded proof that `U_K^m` lies
in the kernel. The published theorem
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk`
(M146.009) has type
`integerUnitsModPrincipalUnitsAtLevelLift_mkStatement m f h x`, which unfolds
to `integerUnitsModPrincipalUnitsAtLevelLift m f h (integerUnitsModPrincipalUnitsAtLevelMk K m x) = f x`.
Applied at level `m` with `f = integerUnitsModPrincipalUnitsAtLevelMk K n`, it
gives exactly the unfolded target. The kernel-containment argument is left as
`_` and is filled by unification with the target, which, after unfolding
`integerUnitsModPrincipalUnitsMapOfLe`, contains the definition's own proof
`h₀`. The two `Statement` types agree up to unfolding of these definitions, so
the term is accepted at the target type.

No auxiliary declaration is introduced.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L39-L48):
the docstring at line 39, the `@[simp]` attribute at line 40 and the theorem
at lines 41–48 (telescope and conclusion at 41–46, proof term at 47–48); the
task's unit range 41–50 ends before the next declaration at 51. The retained
original file has SHA-256
`cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`. The
source proof term is

```lean
  integerUnitsModPrincipalUnitsAtLevelLift_mk m
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe_mk` | `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe_mk` |
| Its statement | `integerUnitsModPrincipalUnitsMapOfLe_mkStatement K hnm x` |
| Used `CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk` | Published `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; omit the `@[simp]` attribute, because the theorem's type is a
`Statement` application rather than an equation that `simp` could use;
replace the source imports by the two imports below; omit the source
`noncomputable section` and all other source declarations. The name,
docstring, telescope and proof term are unchanged. The partition records no
patch10 change to this module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
  supplies the target and, through `...QuotientTower.Maps.Definitions`, the
  map `integerUnitsModPrincipalUnitsMapOfLe`, the quotient
  `IntegerUnitsModPrincipalUnitsAtLevel`, its class map
  `integerUnitsModPrincipalUnitsAtLevelMk` and its lift
  `integerUnitsModPrincipalUnitsAtLevelLift`.
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U009.Proofs`
  is the published proof module of `integerUnitsModPrincipalUnitsAtLevelLift_mk`.

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
unchanged [LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) have SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker
750 adapted this proof directly from the pinned original. The statement is
Worker 5264's, used unchanged.

This module proves only M147.002. The successor-level case M147.004 is a
separate unit.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
