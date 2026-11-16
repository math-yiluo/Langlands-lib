# Exactness of the principal-unit quotient tower at the middle term

This module proves
`Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker`,
the proof phase of M147.013 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m145-m168.md#m147).
Its type is exactly the target
`Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement`
applied to the theorem's parameters.

## Theorem and target

```lean
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement K n
```

The parameters are the target's parameters in the target's order: a field
`K` in an arbitrary universe `u` with a `ValuativeRel K` instance and a level
`n`. The target unfolds to

```lean
MonoidHom.range (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) =
  MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n)
```

that is, `U_K^n/U_K^(n+1) → 𝒪[K]ˣ/U_K^(n+1) → 𝒪[K]ˣ/U_K^n` is exact at the
middle term. No hypothesis is added.

## Implemented proof

```lean
  unfold principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := principalUnitsSuccQuotMk_surjective K n x
    rw [MonoidHom.mem_ker]
    change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
    exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n (u : 𝒪[K]ˣ)).2 u.2
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    rw [MonoidHom.mem_ker] at hq
    change integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 at hq
    have hx : x ∈ principalUnits K n :=
      (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1 hq
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, rfl⟩
```

After `unfold`, `ext q` reduces the equality of subgroups to membership of a
class `q : IntegerUnitsModPrincipalUnitsAtLevel K (n + 1)`, and `constructor`
splits the two inclusions.

1. Range in kernel. An element of the range has the form
   `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n x`. The
   published `Langlands.NYLL.LocalFieldTheory.principalUnitsSuccQuotMk_surjective`
   (M132.040; its type unfolds to
   `Function.Surjective (principalUnitsSuccQuotMk K n)`) writes `x` as
   `principalUnitsSuccQuotMk K n u` for a principal unit `u ∈ U_K^n`.
   After Mathlib's `MonoidHom.mem_ker`, the goal is that the successor map
   sends this element to `1`. `change` replaces the image by
   `integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ)`: the published
   maps M147.010 and M147.003 are Mathlib quotient lifts, the class maps are
   `QuotientGroup.mk'`, and a lift applied to a class reduces to the lifted
   homomorphism applied to the representative (the evaluations recorded by
   the M147.011 and M147.004 statements). The reverse direction of the
   published `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`
   (M146.010; its type unfolds to
   `integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔ x ∈ principalUnits K n`)
   with `u.2` closes it. This is the content of M147.012 at one element.
2. Kernel in range. After reverting the membership, the published
   `Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel.inductionOn`
   (M146.007) at level `n + 1`, with the displayed motive, reduces the claim
   to a class `integerUnitsModPrincipalUnitsAtLevelMk K (n + 1) x` of a unit
   `x : 𝒪[K]ˣ`. Its published type is the Statement
   `IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement`, which unfolds
   to `motive q`, so `refine` accepts it against the goal. The kernel
   hypothesis `hq` becomes, by `MonoidHom.mem_ker` and the same definitional
   `change`, `integerUnitsModPrincipalUnitsAtLevelMk K n x = 1`. The forward
   direction of `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` gives
   `hx : x ∈ principalUnits K n`, so `u = ⟨x, hx⟩` is a principal unit. The
   range witness is `principalUnitsSuccQuotMk K n u`; its image equals the
   class of `x` by `rfl`, the definitional evaluation that M147.011 records.

No auxiliary declaration is introduced, and no unpublished theorem is used.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean#L211-L238):
the docstring at lines 211–212 and the theorem at lines 213–238 (telescope
and conclusion at 213–216, tactics at 217–238); the task's unit range
213–240 ends before the next declaration at 241. The retained original file
has SHA-256 `cf20a6dc5c15aed9dd8d1b20516df5d316228ce73987c161426cc4e179a744a9`.
The source proof is

```lean
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change (integerUnitsModPrincipalUnitsSuccMap K n).comp
        (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n) x = 1
    rw [integerUnitsSuccMap_comp_principalUnitsSuccQuot]
    rfl
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    have hx : x ∈ principalUnits K n := by
      exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1
        (by simpa using hq)
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, by
      rw [principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk]⟩
```

| Original declaration | Adapted declaration |
| --- | --- |
| `CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker` | `Langlands.NYLL.CyclicCohomology.principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker` |
| Its statement | `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement K n` |
| Used `integerUnitsSuccMap_comp_principalUnitsSuccQuot` (first inclusion) | Not used; replaced by the steps of item 1 above |
| Used `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_mk` (witness) | Not used; replaced by `rfl` |
| Used `CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel.inductionOn` | Published `Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel.inductionOn` |
| Used `CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` | Published `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`, by `.1` and `.2` |

Modifications by Worker 750 on 16 November 2026: add the `Langlands.NYLL`
namespace prefix; give the theorem the target applied to its parameters as
its type, unfolded at the start of the proof. The source uses M147.012 for the
first inclusion and M147.011 for the range witness, whose proofs are not yet
in the Library: in the first inclusion, the source `change` to the composite,
`rw` with M147.012 and `rfl` are replaced by the five lines of item 1 (a
representative from the published `principalUnitsSuccQuotMk_surjective`,
`MonoidHom.mem_ker`, the definitional `change` and the reverse direction of
`integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`); the witness's `rw` with
M147.011 is replaced by `rfl`. In the second inclusion, the source
`simpa using hq` inside the proof of `hx` is replaced by
`rw [MonoidHom.mem_ker] at hq` and the definitional `change ... at hq`,
because the source `simp` call evaluates the successor map with the
`@[simp]` lemma M147.004, which is not in the Library; `hx` is then a direct
term. The induction step is
unchanged. Replace the source imports by the three imports below; omit the
source `noncomputable section` and all other source declarations. The name
and docstring are unchanged. The partition records no patch10 change to this
module.

## Imports

- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements`
  supplies the target and, through `...QuotientTower.Maps.Definitions`, the
  two maps, the class maps, and the published proof module
  `...PrincipalUnits.QuotientReps.U010.Proofs` of
  `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff`.
- `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U007.Proofs`
  is the published proof module of
  `IntegerUnitsModPrincipalUnitsAtLevel.inductionOn`.
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U040.Proofs`
  is the published proof module of `principalUnitsSuccQuotMk_surjective`.

These modules and everything they import are left unchanged.

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

This module proves only M147.013; the injectivity M147.014 and the routed
finiteness step M147.025 are separate units.

## Development check

The project Lean service compiled this module in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`) with no errors or warnings; the
theorem has level parameter `u` and uses only `propext`, `Classical.choice`
and `Quot.sound`. This is a development check, not exact-target validation
or independent acceptance.
