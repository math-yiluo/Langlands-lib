# ASCII-named binary induction target (M132.063)

This module gives the published M132.063 target, binary elimination for the actual
maximal-ideal power quotient `MaximalIdealPowSuccQuot K n`, the ASCII name
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn2Statement`.
The proposition says that a two-variable Prop-valued `motive` holds at two
arbitrary quotient classes `q r`, given a proof `h` that it holds at every pair of
classes `maximalIdealPowSuccQuotMk K n a`, `maximalIdealPowSuccQuotMk K n b` of
ideal-power representatives `a b`.

## Why this wrapper exists

The same target is already in the Library as
`Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn₂Statement`, in
`PrincipalUnitQuotients/QuotientAlgebraStatements.lean` (Worker 211). Its name keeps
the source's subscript `₂`. The `lean.proof@1` submission schema accepts only
ASCII qualified Lean names for `proof.declaration` and
`proof.statement_declaration`, so the proof task (Task 5994) cannot submit a
proof of that declaration (operator request `b775bcb973de5bdb975411a14a3d4af2`).
This module adds an ASCII entry point that reuses the published target by name:
its body applies `MaximalIdealPowSuccQuot.inductionOn₂Statement` to the same
arguments. It does not repeat the target's body, and it changes neither the
published file nor its Markdown.

## Source correspondence

| Unit | Source statement lines | Original name | Adapted name |
| --- | --- | --- | --- |
| M132.063 | 833–841 | `LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn₂` | `Langlands.NYLL.LocalFieldTheory.MaximalIdealPowSuccQuot.inductionOn2Statement` (ASCII wrapper of the published `inductionOn₂Statement`) |

The source theorem is represented by a `protected def` returning `Prop`. Its
telescope is the source telescope, the same as that of the published
`inductionOn₂Statement`: implicit `K : Type u` with `[Field K] [ValuativeRel K]`,
explicit `n : Nat`, implicit two-variable `motive`, explicit classes `q r`, and the
explicit representative-wise premise `h`. The body is
`MaximalIdealPowSuccQuot.inductionOn₂Statement (motive := motive) n q r h`, so the
wrapper is definitionally equal to the published target. Unfolding both
definitions gives the source conclusion `motive q r`. `h` stays an explicit
argument, as in the source, and is passed on to the published declaration. The
declaration stays protected. Apart from the `Langlands.NYLL` namespace prefix, the
only changes to the name are that the suffix `On₂` is spelled `On2` and that
`Statement` is appended. The source proof body is omitted. No theorem is proved,
and no axiom or instance is added.

The only import is
`Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements`,
which provides the published `inductionOn₂Statement`. Through its imports it also
provides `MaximalIdealPowSuccQuot` and `maximalIdealPowSuccQuotMk` from
`PrincipalUnitQuotients/MaximalIdealDefinitions.lean`, and Mathlib's `ValuativeRel`
notation `𝒪[K]`, `𝓂[K]`. The source notation scope `open scoped ValuativeRel`,
universe `u` and the noncomputable section are retained. This support unit
discharges no host reciprocity, class-formation or Tate target.

## Provenance and license

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`,
lines 833–841. The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original copyright, Apache-2.0 license and author header are retained. The
Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged.
Worker 5264 wrote this ASCII wrapper.
