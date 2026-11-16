# The successor-level map on a unit class

This module proves
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsSuccMap_mk`,
the proof phase of M147.004 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsSuccMap_mkStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem integerUnitsModPrincipalUnitsSuccMap_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsSuccMap_mkStatement K n x
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance, a level
`n` and a unit `x` of the valuation ring `𝒪[K]`. The target unfolds to

```lean
integerUnitsModPrincipalUnitsSuccMap K n
    (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) =
  integerUnitsModPrincipalUnitsAtLevelMk K n x
```

that is, the successive projection `𝒪[K]ˣ/U_K^(n+1) → 𝒪[K]ˣ/U_K^n` sends the
class of `x` at level `n + 1` to its class at level `n`. No hypothesis is
added.

## Implemented proof

```lean
  (integerUnitsModPrincipalUnitsAtLevelLift_mk (n + 1)
    (integerUnitsModPrincipalUnitsAtLevelMk K n) _ x :
      integerUnitsModPrincipalUnitsMapOfLe_mkStatement K (Nat.le_succ n) x)
```

The published definition `integerUnitsModPrincipalUnitsSuccMap K n` (M147.003)
is `integerUnitsModPrincipalUnitsMapOfLe K (Nat.le_succ n)`, and that map
(M147.001) is the quotient lift
`integerUnitsModPrincipalUnitsAtLevelLift (n + 1) (integerUnitsModPrincipalUnitsAtLevelMk K n) h₀`
with its embedded kernel-containment proof `h₀`. The proof is the M147.002
proof term at `m = n + 1` and `hnm = Nat.le_succ n`:

1. The published theorem
   `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk`
   (M146.009), of type
   `integerUnitsModPrincipalUnitsAtLevelLift_mkStatement (n + 1) f h x`, is
   applied at level `n + 1` with `f = integerUnitsModPrincipalUnitsAtLevelMk K n`.
   Its statement unfolds to
   `integerUnitsModPrincipalUnitsAtLevelLift (n + 1) f h (integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x) = f x`.
2. The term is ascribed the published M147.002 target
   `integerUnitsModPrincipalUnitsMapOfLe_mkStatement K (Nat.le_succ n) x`.
   This ascription makes the elaborator fill the kernel-containment argument
   `_` by unifying with the unfolded M147.002 target, which contains `h₀`;
   without it the placeholder is not synthesized.
3. The M147.002 target at `Nat.le_succ n` and the M147.004 target agree
   after unfolding `integerUnitsModPrincipalUnitsSuccMap`, so the ascribed
   term is accepted at the theorem's type.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L57-L65):
the docstring at line 57, the `@[simp]` attribute at line 58 and the theorem
at lines 59–65 (telescope and conclusion at 59–64, proof term at 65); the
task's unit range 59–67 ends before the next declaration at 68. The retained
original file has SHA-256
`cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`. The
source proof term is

```lean
  integerUnitsModPrincipalUnitsMapOfLe_mk K (Nat.le_succ n) x
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.integerUnitsModPrincipalUnitsSuccMap_mk` | `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsSuccMap_mk` |
| Its statement | `integerUnitsModPrincipalUnitsSuccMap_mkStatement K n x` |
| Used `CyclicCohomology.integerUnitsModPrincipalUnitsMapOfLe_mk` | Its source proof term, from published `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift_mk`, ascribed the M147.002 target |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; omit the `@[simp]` attribute, because the theorem's type is a
`Statement` application; replace the source application of M147.002
`integerUnitsModPrincipalUnitsMapOfLe_mk`, whose proof is not yet in the
Library, by the source proof term of M147.002 at `m = n + 1`, with the type
ascription described above; replace the source imports by the two imports
below; omit the source `noncomputable section` and all other source
declarations. The name, docstring and telescope are unchanged. The partition
records no patch10 change to this module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
  supplies the target, the M147.002 target used in the ascription and,
  through `...QuotientTower.Maps.Definitions`, the maps
  `integerUnitsModPrincipalUnitsSuccMap` and
  `integerUnitsModPrincipalUnitsMapOfLe`, the class map
  `integerUnitsModPrincipalUnitsAtLevelMk` and the lift
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

This module proves only M147.004; M147.002 and the surjectivity M147.005 are
separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
