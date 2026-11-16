# NYLL M353.033: one replacement preserves a different coefficient

The theorem `Langlands.NYLL.PortInternal.M353.d033` proves the published
proposition `Langlands.NYLL.PortInternal.M353.d033Statement`. It imports
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.StepStatements`.
The target and all its imported Lean/Markdown pairs are unchanged.

## Original source and correspondence

The original is Naganori Yamaguchi's
`LubinTate.SameUniformizer.coeff_replacementStep_eq_of_ne`, at lines
566–578 of
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`
in `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The signature occupies lines
566–574 and its proof lines 575–578. The readable pinned file is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered source collections are
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL erratum was found in the Library's `notes/errata/`.
No patch10 edit affects this source module.

The effective section parameters from source lines 29–38 are preserved:
implicit `{K : Type u}`, `[Field K]`, `{F : LocalField.{u, v} K}`,
`{sigma : Type w}` and `[Fintype sigma]`, with independent universes
`u`, `v`, `w`. The theorem then has implicit `L` and `m`, followed by
explicit `hm : 2 ≤ m`, `target`, `H`, `q`, `d`, and `hqd : q ≠ d`,
in exactly that order. Both `q` and `d` belong to
`{d : sigma →₀ ℕ // d.degree = m}`. Its conclusion is the unchanged
Statement application, which unfolds to

```text
MvPowerSeries.coeff q.1 (d030 hm target H d).1 =
  MvPowerSeries.coeff q.1 H.1.
```

Here `H : d002 L` is the actual approximation subtype of series with the
prescribed linear term `L`, and `target` is an arbitrary series over the
actual valuation subring of the chosen local field. The source's unused
section parameter `pi` does not occur in this theorem's type. There is no
uniformizer witness or `LubinTateSeries` parameter.

## Implemented proof

The initial `change` unfolds the Statement abbreviation. From
`hqd : q ≠ d`, equality of the underlying exponents would give subtype
equality by `Subtype.ext`, so the proof obtains `hval : q.1 ≠ d.1`.
The published replacement construction has underlying series

```text
H.1 + MvPowerSeries.monomial d.1
  (MvPowerSeries.coeff d.1 target - MvPowerSeries.coeff d.1 H.1).
```

The final `simp` unfolds `d030`, distributes coefficient extraction over
addition, and applies `MvPowerSeries.coeff_monomial_ne hval`. The monomial
contributes zero to the coefficient at `q.1`, leaving the coefficient of
`H.1`. The proof adds no mathematical premise and uses no other
replacement coefficient-law theorem. The `hm` and equal-degree data
remain as required by the published construction and exact signature.

## Adaptations and preparation credit

The original mathematical proof is by Naganori Yamaguchi, with the
original author header recording assistance by OpenAI Codex. Worker 294
prepared the focused source adaptation for Task 6116
(`c6ac604a-2c1d-4aae-94b5-181c90f66897`), shared in draft revision 2,
content key
`74b79aa672efac8624d3a8819ec67588df2ce020becf8a09a785afd6049080ee`,
at this same module path. Worker 294 renamed the source-private theorem
to `d033`, `Approximation` to `d002`, and `replacementStep` to `d030`;
qualified the namespaces by `Langlands.NYLL`; replaced the original
broad recursive-module imports with the focused published
`Replacement.StepStatements` import; and expressed the conclusion as
the published Statement application, adding `change` before the source
proof. These edits preserve the source hypotheses and binder order.

Worker 797 reused that proof preparation for Task 6934
(`368a2b88-17aa-4e2f-9f45-e71e146c52f2`), checked the pinned original
and published dependencies, retained the proof body and signature,
and expanded this final source, proof and attribution documentation.
Worker 294 is credited as a coauthor of the submission.

The original 2026 copyright, Apache-2.0 release and authorship header is
retained verbatim in the Lean file. The existing `licenses/NYLL/LICENSE`
(SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. The added modification notice credits both workers
without replacing the original authorship.
