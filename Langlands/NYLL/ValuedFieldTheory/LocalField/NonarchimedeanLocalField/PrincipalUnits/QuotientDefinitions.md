# Integer units modulo a principal-unit subgroup (M131.008, M131.009, M131.011)

For any `K : Type u`, `[Field K]`, a supplied `[ValuativeRel K]` and `n : Nat`,
this module constructs the actual quotient group
`𝒪[K]ˣ ⧸ principalUnits K n` of the units of the valuation ring by the `n`-th
principal-unit subgroup `{a ∈ 𝒪[K]ˣ | a - 1 ∈ 𝓂[K]^n}`, its commutative group
structure and its canonical quotient homomorphism. The subgroup is the
published `Langlands.NYLL.LocalFieldTheory.principalUnits` (M131.001); the
integer ring, its units and the quotient group are the canonical Mathlib
constructions. Every natural index, including `0`, is allowed. No positivity,
topology, completeness, discreteness or local-field premise is added.

The complete source-to-Library map is below. Every adapted name has prefix
`Langlands.NYLL.LocalFieldTheory.`; each original has prefix `LocalFieldTheory.`.
The line ranges include the documentation comment and end with the declaration body.

| Unit | Source lines | Kind | Original and adapted suffix | Meaning |
| --- | --- | --- | --- | --- |
| M131.008 | 96–99 | `def` | `IntegerUnitsPrincipalQuot` | The type `𝒪[K]ˣ ⧸ principalUnits K n`, in universe `u` |
| M131.009 | 101–107 | `instance` | `integerUnitsPrincipalQuotCommGroup` | Canonical commutative quotient-group structure on that type |
| M131.011 | 118–122 | `def` | `integerUnitsPrincipalQuotMk` | Canonical quotient homomorphism `𝒪[K]ˣ →* IntegerUnitsPrincipalQuot K n` |

All three telescopes are exactly `(K : Type u) [Field K] [ValuativeRel K] (n : Nat)`,
with these binder kinds and in this order; the single universe `u` is retained.
With `open scoped ValuativeRel`, the interfaces are:

```lean
IntegerUnitsPrincipalQuot.{u} (K : Type u) [Field K] [ValuativeRel K] (n : Nat) : Type u
integerUnitsPrincipalQuotCommGroup.{u} (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
  CommGroup (IntegerUnitsPrincipalQuot K n)
integerUnitsPrincipalQuotMk.{u} (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
  𝒪[K]ˣ →* IntegerUnitsPrincipalQuot K n
```

All three declaration bodies are copied unchanged:

- `IntegerUnitsPrincipalQuot K n` is the plain definition `𝒪[K]ˣ ⧸ principalUnits K n`,
  Mathlib's quotient of a group by a subgroup.
- The instance body is `change CommGroup (𝒪[K]ˣ ⧸ principalUnits K n)` followed by
  `infer_instance`; it therefore is Mathlib's quotient commutative-group structure
  (`QuotientGroup.Quotient.commGroup`, available because `𝒪[K]ˣ` is commutative and
  every subgroup of a commutative group is normal).
- The quotient map body is `change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K n)` followed by
  `exact QuotientGroup.mk' (principalUnits K n)`.

A focused check confirmed that the type, the instance and the map are
definitionally (`rfl`) `𝒪[K]ˣ ⧸ principalUnits K n`,
`QuotientGroup.Quotient.commGroup (principalUnits K n)` (the instance found by
`inferInstance` on that quotient), and `QuotientGroup.mk' (principalUnits K n)`.
No separate quotient model or assumed equivalence is used.

The instance is a global instance in the source namespace, exactly as in the
source; it is not scoped or local. It lives on the new type
`IntegerUnitsPrincipalQuot K n`, which is a definition rather than an abbreviation,
so it exposes the canonical structure of this new type and does not duplicate or
replace any existing Mathlib or Library instance.

M131.010 (`integerUnitsPrincipalQuotConcreteEquiv`, source lines 109–116) is not
ported: none of the six units of Task 5856 uses it, since the quotient map and
the induction principle reach the concrete quotient with `change` instead.
Source lines 124–184 (M131.012–M131.018: theorems and the lift) are not part of
this task. The theorem units M131.005, M131.019 and M131.020 are published as
Prop-valued targets in the sibling module `AntitoneQuotientStatements`.

## Modifications

- The source namespace `LocalFieldTheory` is prefixed by `Langlands.NYLL`.
- The source import `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic`
  is replaced by exactly these two imports:
  - `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`,
    which supplies the published `principalUnits` and, through its own imports,
    the valuation-ring notation `𝒪[K]`;
  - `Mathlib.GroupTheory.QuotientGroup.Basic`, which supplies the quotient group,
    its commutative-group instance and `QuotientGroup.mk'`.
- The source module documentation, which describes the whole source file, is
  replaced by documentation of these three declarations.
- Only these three declarations are extracted. The source `noncomputable section`,
  `universe u` and `open scoped ValuativeRel` are retained; the source has no other
  `open` command. No theorem command of the source file is copied.

There are no other changes. Declaration names, documentation strings,
telescopes and bodies are as in the source. This module introduces no
axiom, no proof hole and no additional instance, and supplies no host
reciprocity, class-formation or Tate result.

## Source and license

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean`
(inventory module M131). The complete source file SHA-256 is
`1b36c019d270961f321ca891ae155fb4fd658d4e29ed97ba78e30fbee00a5047`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum is recorded in the published port plan
`notes/reuse/nyll-public-port-plan.md`.

The original copyright, Apache-2.0 license and author header are retained, followed
by a dated modification record. The Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged; their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 346 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
