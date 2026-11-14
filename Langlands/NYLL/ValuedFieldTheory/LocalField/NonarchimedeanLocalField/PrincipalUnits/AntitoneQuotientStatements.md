# Antitonicity, quotient induction and a unit identity: targets (M131.005, M131.019, M131.020)

These are three Prop-valued targets. Throughout, `K : Type u` is an arbitrary field
with a supplied `[ValuativeRel K]`, `𝒪[K]` is its valuation ring and
`principalUnits K n = {a ∈ 𝒪[K]ˣ | a - 1 ∈ 𝓂[K]^n}` is the published
principal-unit subgroup (M131.001).

- M131.005 states that for natural numbers `m ≤ n`,
  `principalUnits K n ≤ principalUnits K m`: the filtration decreases.
- M131.019 states that a Prop-valued `motive` on the quotient
  `IntegerUnitsPrincipalQuot K n = 𝒪[K]ˣ ⧸ principalUnits K n` holds at a class `q`,
  given that it holds at `integerUnitsPrincipalQuotMk K n u` for every unit `u`.
- M131.020 states the ring identity
  `ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)` in `𝒪[K]` for two units `a b` of
  `𝒪[K]`, with the product taken in `𝒪[K]ˣ` and coerced to `𝒪[K]`.

All retain the exact arbitrary-field signature; no topology, completeness,
discreteness, local-field or positivity premise is added, and every natural index,
including `0`, is allowed.

All original names in this table have prefix `LocalFieldTheory.` and all adapted
names have prefix `Langlands.NYLL.LocalFieldTheory.`. The statement line ranges
start at the declaration keyword and end at the original conclusion, before the
source proof; the documentation comment lies immediately above.

| Unit | Source kind | Documentation lines | Statement lines | Original suffix | Adapted suffix |
| --- | --- | --- | --- | --- | --- |
| M131.005 | `theorem` | 78 | 79–81 | `principalUnits_antitone` | `principalUnits_antitoneStatement` |
| M131.019 | `protected theorem` | 186–187 | 188–193 | `IntegerUnitsPrincipalQuot.inductionOn` | `IntegerUnitsPrincipalQuot.inductionOnStatement` |
| M131.020 | `lemma` | 199 | 200–203 | `unit_mul_sub_one_eq` | `unit_mul_sub_one_eqStatement` |

## Exact telescopes

Each original theorem or lemma becomes a `def` returning `Prop`, whose parameters
are the complete source telescope and whose body is exactly the source
conclusion. Every source universe, parameter, instance, binder kind and binder
order is retained; the single universe `u` is unchanged. With
`open scoped ValuativeRel`, the interfaces are:

```lean
principalUnits_antitoneStatement.{u} (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) : Prop :=
  principalUnits K n ≤ principalUnits K m

protected IntegerUnitsPrincipalQuot.inductionOnStatement.{u}
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : IntegerUnitsPrincipalQuot K n → Prop}
    (q : IntegerUnitsPrincipalQuot K n)
    (h : ∀ u : 𝒪[K]ˣ, motive (integerUnitsPrincipalQuotMk K n u)) : Prop :=
  motive q

unit_mul_sub_one_eqStatement.{u} (K : Type u) [Field K] [ValuativeRel K]
    (a b : 𝒪[K]ˣ) : Prop :=
  ((a * b : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
    ((a : 𝒪[K]) - 1) * ((b : 𝒪[K]) - 1) +
      ((a : 𝒪[K]) - 1) + ((b : 𝒪[K]) - 1)
```

In M131.005, `K` is explicit, `m n` are implicit and the premise `h : m ≤ n` is
explicit. In M131.019, `K` is implicit, `n` explicit, `motive` implicit, the class
`q` explicit and the representative-wise proof `h` explicit; the declaration
remains protected. In M131.020, `K`, `a` and `b` are explicit. The coercions in
M131.020 are the source's exact unit and subtype coercions.

In M131.005 and M131.019 the explicit proof premise `h` is retained under its
source name even though it does not occur in the conclusion. Each of these two
declarations is therefore preceded by `set_option linter.unusedVariables false in`,
which only silences the unused-variable linter for that one declaration and does
not change its type or value. A proof of either target is a function of all its
parameters, including `h`.

The quotient type and map are the definitions
`Langlands.NYLL.LocalFieldTheory.IntegerUnitsPrincipalQuot` and
`Langlands.NYLL.LocalFieldTheory.integerUnitsPrincipalQuotMk` (M131.008, M131.011)
of this task's sibling module `QuotientDefinitions`; they are definitionally
`𝒪[K]ˣ ⧸ principalUnits K n` and `QuotientGroup.mk' (principalUnits K n)`.

A focused check confirmed that the three source proofs, copied unchanged after a
`show` of the original conclusion, prove these targets applied to the source
telescopes. That check is evidence of fidelity only; no proof is published here.

## Modifications

- The source namespace `LocalFieldTheory` is prefixed by `Langlands.NYLL`.
- Each theorem or lemma becomes a Prop-valued `def` whose name receives only the
  suffix `Statement`; the protected declaration remains protected.
- The source proofs, from `:= by` on lines 81, 193 and 203 through lines 83, 197
  and 205 respectively, are omitted.
  No theorem is proved and no axiom or instance is added. The source theorems
  carry no attributes.
- The two `set_option linter.unusedVariables false in` commands described above
  are added, each with a one-line comment.
- The source import `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic`
  is replaced by the single import
  `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.QuotientDefinitions`,
  which supplies the quotient type and map and, through its own imports, the
  published `principalUnits` and the valuation-ring notation.
- The source module documentation is replaced by documentation of these three
  targets. The source `noncomputable section`, `universe u` and
  `open scoped ValuativeRel` are retained; the source has no other `open` command.
  Documentation strings are as in the source.

There are no other mathematical changes. This support unit discharges no host
reciprocity, class-formation, cup, transfer or Tate target.

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
