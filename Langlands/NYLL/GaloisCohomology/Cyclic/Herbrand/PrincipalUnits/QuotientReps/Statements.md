# Statement targets for integer-unit quotients at a level

This module contains three Prop-valued definitions in
`Langlands.NYLL.CyclicCohomology`. Each keeps the complete telescope of its
source theorem and has the source conclusion as its body. It supplies
statement targets; it does not supply proofs of them.
It imports only the paired `QuotientReps.Definitions` module.

For every arbitrary field `K : Type u` with `[Field K] [ValuativeRel K]`,
the actual named quotient is
`IntegerUnitsModPrincipalUnitsAtLevel K n = 𝒪[K]ˣ ⧸ principalUnits K n`.
The canonical quotient projection and the quotient lift are the source
constructions in that imported module. Every natural level, including zero,
is retained, without additional local-field, topology, finiteness,
completeness, discreteness or nontrivial-valuation assumptions.

With `open scoped ValuativeRel` and
`open Langlands.NYLL.LocalFieldTheory`, the full definitions are:

```lean
protected def IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsModPrincipalUnitsAtLevel K n → Prop}
    (q : IntegerUnitsModPrincipalUnitsAtLevel K n)
    (h : ∀ x : 𝒪[K]ˣ,
      motive (integerUnitsModPrincipalUnitsAtLevelMk K n x)) :
    Prop :=
  motive q

def integerUnitsModPrincipalUnitsAtLevelLift_mkStatement
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (n : Nat) (f : 𝒪[K]ˣ →* M) (h : principalUnits K n ≤ f.ker)
    (x : 𝒪[K]ˣ) : Prop :=
  integerUnitsModPrincipalUnitsAtLevelLift n f h
      (integerUnitsModPrincipalUnitsAtLevelMk K n x) = f x

def integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) (x : 𝒪[K]ˣ) : Prop :=
  integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 ↔
    x ∈ principalUnits K n
```

The first target is the representative induction rule. Its motive is
Prop-valued, its field and motive binders are implicit, and `n`, `q`, `h`
are explicit in exactly that order. The representative hypothesis `h` remains
in the telescope even though the conclusion `motive q` does not mention it.
The second target is the lift's evaluation formula. Its independently
universed target `M : Type*` has only a group structure, and the kernel
inclusion `h` remains an explicit argument after `n` and `f`, before `x`.
The third target says that a canonical quotient class is the identity
exactly when its representative is in the level subgroup. Its field `K` is
explicit, as in the source. No binder is strengthened, reordered or removed.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientReps.lean).
Its exact file SHA-256 is
`0165f6ca2068526dbcf038b890ae51cfeebdc9ed4838cb60425a458a265f3996`.

Every original name below has prefix `CyclicCohomology.`;
every adapted name has prefix `Langlands.NYLL.CyclicCohomology.`.

| Unit | Original suffix | Adapted suffix | Exact source lines |
| --- | --- | --- | --- |
| M146.007 | `IntegerUnitsModPrincipalUnitsAtLevel.inductionOn` | `IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement` | telescope/conclusion 75–81; docstring 74; excluded proof 82–85 |
| M146.009 | `integerUnitsModPrincipalUnitsAtLevelLift_mk` | `integerUnitsModPrincipalUnitsAtLevelLift_mkStatement` | telescope/conclusion 97–102; docstring/attribute 95–96; excluded proof 103 |
| M146.010 | `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` | `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement` | telescope/conclusion 106–109; docstring 105; excluded proof 110–111 |

The namespace gains the `Langlands.NYLL` prefix and
`open LocalFieldTheory` becomes `open Langlands.NYLL.LocalFieldTheory`.
The broad source import of
`Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients`
is replaced by the selected `QuotientReps.Definitions` import, which supplies
all dependencies of these statements.
Each `theorem` becomes a `def` with the specified `Statement` suffix.
Its original conclusion becomes the body of the Prop-valued definition and
the proof is omitted. The source's `protected` modifier is retained for the
induction target. The `[simp]` attribute on the source lift theorem is omitted
because the adaptation is a proposition definition.
Docstrings and the module overview now describe targets.
The source `noncomputable section`, `universe u`, `Type*` binder,
notation scope, full source parameter names, binder kinds and order are
preserved. `set_option linter.unusedVariables false` suppresses the warning
for the induction hypothesis retained in the telescope; it does not change
the proposition or elaborated signature. These are all modifications.
No private or anonymous source command or unlisted source theorem is needed.

Mathlib supplies generic `QuotientGroup.induction_on`,
`QuotientGroup.lift_mk` and `QuotientGroup.eq_one_iff`; these explain the
source's quotient interface. The targets retain the exact namespaced source
statements instead of silently adapting their telescopes to generic ones.
Exact-name searches found no existing required target in the Library or
Mathlib. The actual quotient and principal-unit definitions are reused by
Lean name.

The original is registered as `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained registered source was read directly; no applicable NYLL errata
note was found. The original copyright, license and author header is retained.
The Library's unchanged `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`
have SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No compatibility patch or another worker's unpublished draft is reused.
These support targets discharge no host class-formation, cup-product,
transfer, Tate-cohomology or reciprocity target.

## Focused checks

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, each target
was inspected with the statement entry module last in dependency order:

| Target suffix | Successful check | Returns Prop |
| --- | --- | --- |
| `IntegerUnitsModPrincipalUnitsAtLevel.inductionOnStatement` | `915d8679-051a-49f8-8027-b26d2c13f3e4` | true |
| `integerUnitsModPrincipalUnitsAtLevelLift_mkStatement` | `ffb079b1-293f-4b94-947a-badd70f2675e` | true |
| `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iffStatement` | `26e8c989-4838-4794-bbc9-9e791d993d40` | true |

All returned `ok: true`, exit code zero and no errors or warnings.
The lift target retains separate universe parameters `u` and `u_1`;
the other targets have only `u`. Their inspected assumptions are only
`propext`, `Classical.choice` and `Quot.sound`.
Private check `e5c2f8a0-85c3-42fb-8c52-f3adb682a6a3` also compiled direct
assignments of the three unapplied target constants to complete source
telescopes, and reflexive equalities of each target body with its source
conclusion. It returned no errors or warnings. Those examples check
signatures and proposition definitions; they do not prove these targets.
Independent semantic acceptance and publication remain separate requirements.
