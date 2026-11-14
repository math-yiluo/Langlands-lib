# The linear form has zero constant coefficient: proof of NYLL M347.002

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_linearForm`
in module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.U002.Proofs`
proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.constantCoeff_linearFormStatement`
from module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements`.
That statement module is the only import and is left unchanged, as are the
`Definitions` module it imports and their Markdown files.

## Target and mathematical meaning

The theorem has the parameters of the published target:
implicit `{R : Type u} [CommRing R]`, implicit `{σ : Type v} [Fintype σ]`
(independent universes `u` and `v`), and explicit `(L : σ → R)`.
Its type is exactly `constantCoeff_linearFormStatement L`, which unfolds to

```lean
MvPowerSeries.constantCoeff (linearForm L) = 0
```

Here `linearForm L` is the published definition
`∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`.
Mathematically: for every commutative ring `R` and finite variable type `σ`,
the multivariable linear form `∑ᵢ Lᵢ Xᵢ` has zero constant coefficient.
There is no field, local-field, nontriviality, nonempty-variable or other
extra hypothesis.

## Implemented proof

The proof is two tactic steps (`Proofs.lean`, lines 50–51):

1. `unfold constantCoeff_linearFormStatement` turns the goal into
   `MvPowerSeries.constantCoeff (linearForm L) = 0`.
2. `simp [linearForm]` (the unchanged source tactic) unfolds the linear form
   to the finite sum. The simp set then rewrites the ring homomorphism
   `MvPowerSeries.constantCoeff` through the sum and the products.
   Mathlib's simp lemmas `constantCoeff_C` and `constantCoeff_X` send each
   summand to `L i * 0 = 0`, and the sum of zeros is zero.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## The `@[simp]` attribute

The theorem carries `@[simp]`, as in the source (line 32). Because the
published target is an ordinary (semireducible) `def` rather than an
`abbrev`, a bare `@[simp]` would not reproduce the source lemma. Lean
preprocesses a simp theorem at reducible transparency, so it would see only the
proposition `constantCoeff_linearFormStatement L` and register the rewrite
`constantCoeff_linearFormStatement L = True`. A development check confirmed
that with a bare attribute, `simp` cannot prove
`a + MvPowerSeries.constantCoeff (linearForm L) = a`.

The declaration is therefore preceded (lines 43–44) by

```lean
set_option allowUnsafeReducibility true in
attribute [local reducible] constantCoeff_linearFormStatement in
```

These commands make the target proposition reducible only while this
theorem is elaborated and its attributes are applied. Simp's preprocessing
then sees the source equation
`MvPowerSeries.constantCoeff (linearForm L) = 0`. It adds this equation to the
global simp set through Lean's usual auxiliary simp lemma, with left-hand side
`MvPowerSeries.constantCoeff (linearForm L)`.

Lean requires the `allowUnsafeReducibility` option for a local `[reducible]`
override because simp and instance indexes unfold reducible constants.
Here the registered left-hand side does not contain
`constantCoeff_linearFormStatement`, so its index keys are the same as in an
ordinary context. Reducibility has no effect on the kernel. The theorem's type
is unchanged: its inspected type fingerprint is the same with and without the
override.

A private development test importing this module checked these points:

- After import, `constantCoeff_linearFormStatement` is still
  `semireducible`.
- The default `simp` closes `MvPowerSeries.constantCoeff (linearForm L) = 0`
  and `a + MvPowerSeries.constantCoeff (linearForm L) = a`. For the second goal,
  `simp?` reports `simp only [constantCoeff_linearForm, add_zero]`.
- The source proof of M347.004 (source lines 50–54, ending
  `simpa using hconstant`) compiles unchanged downstream.

One remaining difference from the source: an explicit
`simp only [constantCoeff_linearForm]` re-preprocesses the constant where it is
used, where the target is semireducible again, so it gets only the `= True`
form. Callers who need the equation explicitly can use the term
`constantCoeff_linearForm L`, whose type unfolds definitionally to the
equation, or rely on the default simp set.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`, lines 31–35](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean#L31-L35).
The theorem signature is at lines 33–34, `@[simp]` at line 32, the docstring
at line 31 and the proof `simp [linearForm]` at line 35. The section variables
are at lines 24–25. The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean`.
Worker 463 recomputed its SHA-256,
`154a6f23a3514dce4d5b450d51a65db7d3038029c43a56b58f95faecb7d3872d`,
on 14 November 2026.

| Source (namespace `LubinTate.SameUniformizer`) | Adapted |
| --- | --- |
| `@[simp]`, line 32 | `@[simp]`, line 47, with the reducibility override above |
| `theorem constantCoeff_linearForm (L : σ → R)`, line 33 | Same name under `Langlands.NYLL.`, line 48 |
| Conclusion `MvPowerSeries.constantCoeff (linearForm L) = 0`, line 34 | `constantCoeff_linearFormStatement L`, line 49 (the published target, definitionally the source conclusion) |
| Proof `simp [linearForm]`, line 35 | `unfold constantCoeff_linearFormStatement` followed by the same `simp [linearForm]`, lines 50–51 |
| Variables `{R : Type*} [CommRing R]`, `{σ : Type*} [Fintype σ]`, lines 24–25 | `{R : Type u} [CommRing R]`, `{σ : Type v} [Fintype σ]`, lines 34–35 |

All adaptations, made by Worker 463 on 14 November 2026:

- Extract only theorem M347.002; the definitions `linearForm` and
  `HasLinearTerm` are imported from the published `Definitions` module (through
  `Statements`), and the other theorems belong to separate tasks.
- Prefix the namespace with `Langlands.NYLL`, written as one `namespace`
  command.
- Import the published `Statements` module instead of the source imports
  `Mathlib.RingTheory.MvPowerSeries.Order` and
  `Mathlib.RingTheory.PowerSeries.Substitution`, which it supplies.
- Name the two independent universes `u` and `v` explicitly in place of the
  source's two `Type*` binders, matching the published target.
- State the conclusion as the published proposition and add the one
  `unfold` step before the source tactic.
- Add the command-scoped reducibility override described above, so that the
  retained `@[simp]` registers the source equation.
- Replace the source docstring "States the theorem `constantCoeff_linearForm`."
  with a statement of the result, and add a module description.
- Omit the unused `noncomputable section` wrapper.
- Add a dated modification notice after the original header.

No public auxiliary declaration or instance is added. The `@[simp]` attribute
on this theorem is the only global attribute.

## Attribution and licence

The Lean file keeps the original header verbatim: "Copyright (c) 2026
Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Authors:
Naganori Yamaguchi (assisted by OpenAI Codex)". Worker 463's dated
modification notice follows it. The existing
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) apply and
are not modified.

The pinned source is registered as `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No patch10 edit applies to this unit.

## Development verification

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiles with
no errors or warnings. The inspected theorem has level parameters `u` and `v`
and depends only on `propext`, `Classical.choice` and `Quot.sound`.
Compilation is not acceptance: publication under `lean.proof@1` also requires
the Lake build, exact-target and unchanged-statement checks, independent
semantic review and integration.
