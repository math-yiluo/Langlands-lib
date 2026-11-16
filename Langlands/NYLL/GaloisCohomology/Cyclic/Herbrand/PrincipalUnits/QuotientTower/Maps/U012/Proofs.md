# The composite of the graded inclusion and the successor map is trivial

This module proves
`Langlands.NYLL.CyclicCohomology.integerUnitsSuccMap_comp_principalUnitsSuccQuot`,
the proof phase of M147.012 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem integerUnitsSuccMap_comp_principalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement K n
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance and a level
`n`. The target unfolds to

```lean
(integerUnitsModPrincipalUnitsSuccMap K n).comp
    (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) = 1
```

that is, the composite
`U_K^n/U_K^(n+1) → 𝒪[K]ˣ/U_K^(n+1) → 𝒪[K]ˣ/U_K^n` is the trivial
homomorphism. No hypothesis is added.

## Implemented proof

```lean
  unfold integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement
  ext q
  obtain ⟨u, rfl⟩ := principalUnitsSuccQuotMk_surjective K n q
  rw [MonoidHom.comp_apply, MonoidHom.one_apply]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n (u : 𝒪[K]ˣ)).2 u.2
```

1. `unfold` exposes the equation of homomorphisms, and `ext q` reduces it to
   the pointwise equation at a class `q : PrincipalUnitsSuccQuot K n`.
2. The published theorem
   `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjective`
   (M132.040), of type `principalUnitsSuccQuotMk_surjectiveStatement K n`,
   which unfolds to `Function.Surjective (principalUnitsSuccQuotMk K n)`,
   gives a principal unit `u : principalUnits K n` with
   `principalUnitsSuccQuotMk K n u = q`; `rfl` substitutes this for `q`.
3. Mathlib's `MonoidHom.comp_apply` and `MonoidHom.one_apply` turn the goal
   into
   `integerUnitsModPrincipalUnitsSuccMap K n (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n (principalUnitsSuccQuotMk K n u)) = 1`.
4. `change` replaces the left side by
   `integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ)`. This is a
   definitional equality: the published maps M147.010 and M147.003 are
   Mathlib quotient lifts (`QuotientGroup.lift`) and the class maps are
   `QuotientGroup.mk'`, and a lift applied to a class reduces to the lifted
   homomorphism applied to the representative. These are the two evaluations
   that the M147.011 and M147.004 statements record.
5. The published theorem
   `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`
   (M146.010), whose type unfolds to
   `integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔ x ∈ principalUnits K n`,
   is used in its reverse direction at `x = (u : 𝒪[K]ˣ)` with the
   membership `u.2 : (u : 𝒪[K]ˣ) ∈ principalUnits K n`.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L190-L209):
the docstring at line 190 and the theorem at lines 191–209 (telescope and
conclusion at 191–194, tactics at 195–209); the task's unit range 191–212
ends before the next declaration at 213. The retained original file has
SHA-256 `cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`.
The source proof is

```lean
  ext q
  refine PrincipalUnitsSuccQuot.inductionOn n
    (motive := fun q =>
      ((integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n)) q =
          (1 : PrincipalUnitsSuccQuot K n →*
            IntegerUnitsModPrincipalUnitsAtLevel K n) q)
    q ?_
  intro u
  rw [MonoidHom.comp_apply,
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk,
    integerUnitsModPrincipalUnitsSuccMap_mk]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  rw [integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff]
  exact u.2
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.integerUnitsSuccMap_comp_principalUnitsSuccQuot` | `Langlands.NYLL.CyclicCohomology.integerUnitsSuccMap_comp_principalUnitsSuccQuot` |
| Its statement | `integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement K n` |
| Used `LocalFieldTheory.PrincipalUnitsSuccQuot.inductionOn` | Not used; replaced by published `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjective` |
| Used `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk`, `integerUnitsModPrincipalUnitsSuccMap_mk` | Not used; replaced by the definitional `change` |
| Used `CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` | Published `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`, by `.2` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type, unfolded at the start of the proof. The source eliminates the class
`q` with M132.007 `PrincipalUnitsSuccQuot.inductionOn` and rewrites with
M147.011 and M147.004, whose proofs are not yet in the Library: this proof
takes a representative with the published
`principalUnitsSuccQuotMk_surjective` instead, rewrites only with the two
Mathlib `MonoidHom` lemmas and reaches the source's `change` goal directly by
definitional unfolding. The final source `rw` with
`integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` and `exact u.2` become a
single application of the reverse direction of that published theorem,
because its published type is a `Statement` application, which `rw` cannot
use. Replace the source imports by the two imports below; omit the source
`noncomputable section` and all other source declarations. The name and
docstring are unchanged. The partition records no patch10 change to this
module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
  supplies the target and, through `...QuotientTower.Maps.Definitions`, the
  maps `integerUnitsModPrincipalUnitsSuccMap` and
  `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc`, the class
  maps, and the published proof module
  `...PrincipalUnits.QuotientReps.U010.Proofs` of
  `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U040.Proofs`
  is the published proof module of `principalUnitsSuccQuotMk_surjective`.

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

This module proves only M147.012; the exactness M147.013 is a separate unit.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
