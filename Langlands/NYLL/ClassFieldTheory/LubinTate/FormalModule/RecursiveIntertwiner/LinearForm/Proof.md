# The prescribed linear form has its own linear term: proof of NYLL M353.001

The theorem
`Langlands.NYLL.LubinTate.SameUniformizer.linearForm_hasLinearTerm`
in module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearForm.Proof`
proves the published proposition
`Langlands.NYLL.LubinTate.SameUniformizer.linearForm_hasLinearTermStatement`
from module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearForm.Statement`.
That Statement module is the only import. It is unchanged, as are its
Markdown and the modules it imports.

## Target and mathematical meaning

The theorem has the parameters of the published target, with independent
universes `u`, `v` and `w`:

- implicit `{K : Type u} [Field K]`;
- implicit `{F : LocalField.{u, v} K}`;
- implicit `{sigma : Type w} [Fintype sigma]`;
- explicit `(L : sigma → F.valuationSubring)`.

Its type is exactly `linearForm_hasLinearTermStatement L`. This unfolds to

```lean
HasLinearTerm (linearForm L) L
```

and, after unfolding the published `HasLinearTerm`, to
`(2 : ℕ∞) ≤ (linearForm L - linearForm L).order`. Here `linearForm L` is the
published multivariable power series `∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i`
over the valuation subring `F.valuationSubring`, and `.order` is Mathlib's
total order `MvPowerSeries.order`.

Mathematically: for a local field `F` (the shared adapted `LocalField`
package extending `CompleteDVF` with a finite residue field) and a finite
variable type `sigma`, the linear form `∑ᵢ Lᵢ Xᵢ` with coefficients in the
valuation ring has prescribed linear term `L`. The statement is trivial: its
difference from itself is `0`, and `0` has order `⊤`. There is no uniformizer,
Lubin–Tate series, nonempty-variable or other extra hypothesis.

## Implemented proof

The proof is two tactic steps (`Proof.lean`, lines 47–48):

1. `unfold linearForm_hasLinearTermStatement` turns the goal into
   `HasLinearTerm (linearForm L) L`, the source conclusion.
2. `simp [HasLinearTerm]` (the unchanged source tactic) unfolds the
   definition to `(2 : ℕ∞) ≤ (linearForm L - linearForm L).order`. A private
   `simp?` check reports that it uses exactly
   `simp only [HasLinearTerm, sub_self, MvPowerSeries.order_zero, le_top]`:
   `sub_self` rewrites the difference to `0`, `MvPowerSeries.order_zero`
   rewrites its order to `⊤`, and `le_top` closes `2 ≤ ⊤`.

The `unfold` step is needed. The published target is an ordinary
(semireducible) `def`, and a private check confirmed that the source
tactic alone fails on the goal `linearForm_hasLinearTermStatement L` with
"`simp` made no progress". Private checks importing this module also confirmed
that the term `linearForm_hasLinearTerm L` is accepted at the source type
`HasLinearTerm (linearForm L) L`, so source-style callers can use it directly.

The theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Source correspondence and adaptations

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`, lines 40–44](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean#L40-L44).
The docstring is at line 40, the theorem statement at lines 41–43 and the
proof `simp [HasLinearTerm]` at line 44. The section variables are at
lines 36–38, the `noncomputable section` at line 27 and the universes at
line 29. The readable original is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Worker 463 recomputed its SHA-256,
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`,
on 15 November 2026.
No applicable NYLL erratum was found in the Library's `notes/errata/`.

| Source (namespace `LubinTate.SameUniformizer`) | Adapted |
| --- | --- |
| Docstring, line 40 | Same docstring, line 43 |
| `theorem linearForm_hasLinearTerm (L : sigma → F.valuationSubring)`, lines 41–42 | Same name and binder under `Langlands.NYLL.`, lines 44–45 |
| Conclusion `HasLinearTerm (linearForm L) L`, line 43 | `linearForm_hasLinearTermStatement L`, line 46 (the published target, definitionally the source conclusion) |
| Proof `simp [HasLinearTerm]`, line 44 | `unfold linearForm_hasLinearTermStatement` followed by the same `simp [HasLinearTerm]`, lines 47–48 |
| Variables `{K : Type u} [Field K]`, `{F : LocalField.{u, v} K} {pi : F.valuationSubring}`, `{sigma : Type w} [Fintype sigma]`, lines 36–38 | The same without `pi`, lines 39–41 |
| `open LocalFieldTheory.DiscreteValuationField`, line 34 | `open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`, line 37 |

All adaptations, made by Worker 463 on 15 November 2026:

- Extract only theorem M353.001. The definitions `linearForm`,
  `HasLinearTerm`, `LocalField` and its valuation subring are reused by Lean
  name through the published Statement module. The source overview, the other
  declarations of the source file and its later sections belong to separate
  tasks and are omitted.
- Prefix the namespace and the opened namespace with `Langlands.NYLL`. The
  two source `namespace` commands are written as one.
- Import the published Statement module instead of the source imports
  `Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization` and
  `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection`.
- Omit the section variable `{pi : F.valuationSubring}`. It is not used by
  this theorem, so it is absent from the elaborated source theorem and from
  the published target.
- State the conclusion as the published proposition and add the one `unfold`
  step before the source tactic.
- Add a module description and a dated modification notice after the
  original header.

The source's `noncomputable section`, universe names, variable binders
(other than `pi`), theorem name, explicit binder, docstring and proof tactic
are retained. The theorem has no attribute, as in the source. No auxiliary
declaration, instance or attribute is added.

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
No patch10 edit applies to this source module.

## Use downstream

The stage-zero approximation data M353.016 needs this result. In the source
(line 306) stage zero of the recursive approximation is
`⟨linearForm L, linearForm_hasLinearTerm L⟩`, the linear form as an element of
the subtype of series with prescribed linear term `L`. Because the theorem's
type unfolds definitionally to `HasLinearTerm (linearForm L) L`, the term
`linearForm_hasLinearTerm L` fills that position unchanged: a private check
importing this module elaborated
`⟨linearForm L, linearForm_hasLinearTerm L⟩` at the type
`{H : MvPowerSeries sigma F.valuationSubring // HasLinearTerm H L}`.

## Development verification

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), the module compiles with
no errors or warnings. The inspected theorem has level parameters `u`, `v`
and `w` and depends only on `propext`, `Classical.choice` and `Quot.sound`.
Compilation is not acceptance: publication under `lean.proof@1` also requires
the Lake build, exact-target and unchanged-statement checks, independent
semantic review and integration.
