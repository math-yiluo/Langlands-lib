# The principal-unit quotient map on a representative

This module proves
`Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk`,
the proof phase of M147.011 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (u : principalUnits K n) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement K n u
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance, a level
`n` and a principal unit `u ∈ U_K^n`. The target unfolds to

```lean
principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n
    (principalUnitsSuccQuotMk K n u) =
  integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) (u : 𝒪[K]ˣ)
```

that is, the map `U_K^n/U_K^(n+1) → 𝒪[K]ˣ/U_K^(n+1)` sends the class of `u`
to the class of `u`, viewed as a unit of `𝒪[K]`. No hypothesis is added.

## Implemented proof

```lean
  rfl
```

Both sides reduce to the same term by unfolding published definitions:

1. `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n` (M147.010,
   module `...QuotientTower.Maps.Definitions`) is
   `principalUnitsSuccQuotLift n ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp (principalUnits K n).subtype) h₀`
   for its embedded kernel-containment proof `h₀`.
2. The published `principalUnitsSuccQuotLift n f h` is Mathlib's
   `QuotientGroup.lift ((principalUnits K (n + 1)).subgroupOf (principalUnits K n)) f h`,
   and the published `principalUnitsSuccQuotMk K n` is
   `QuotientGroup.mk' ((principalUnits K (n + 1)).subgroupOf (principalUnits K n))`
   (both in `...PrincipalUnitQuotients.SuccessorDefinitions`).
3. Mathlib's `QuotientGroup.lift f h (QuotientGroup.mk x)` reduces to `f x`,
   so the left side reduces to
   `integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) ((principalUnits K n).subtype u)`,
   and `(principalUnits K n).subtype u` is the coercion `(u : 𝒪[K]ˣ)`.

So `rfl` closes the goal by definitional unfolding. No auxiliary declaration
is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L178-L188):
the docstring at line 178, the `@[simp]` attribute at line 179 and the
theorem at lines 180–188 (telescope and conclusion at 180–185, proof term at
186–188); the task's unit range 180–190 ends before the next declaration at
191. The retained original file has SHA-256
`cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`. The
source proof term is

```lean
  principalUnitsSuccQuotLift_mk n
    ((integerUnitsModPrincipalUnitsAtLevelMk K (n + 1)).comp
      (principalUnits K n).subtype) _ u
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk` | `Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk` |
| Its statement | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mkStatement K n u` |
| Used `LocalFieldTheory.principalUnitsSuccQuotLift_mk` | Not used; replaced by `rfl` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type; omit the `@[simp]` attribute, because the theorem's type is a
`Statement` application; replace the source application of M132.006
`principalUnitsSuccQuotLift_mk`, whose proof is not yet in the Library, by
`rfl`, the definitional evaluation of the quotient lift on a class that this
application expresses; replace the source imports by the single import
below; omit the source `noncomputable section` and all other source
declarations. The name, docstring and telescope are unchanged. The partition
records no patch10 change to this module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
  supplies the target and, through `...QuotientTower.Maps.Definitions`, the
  map `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc`, the class
  maps `principalUnitsSuccQuotMk` and `integerUnitsModPrincipalUnitsAtLevelMk`
  and the lift `principalUnitsSuccQuotLift`.

This module and everything it imports are left unchanged.

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

This module proves only M147.011; the composite M147.012, the exactness
M147.013 and the injectivity M147.014 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
