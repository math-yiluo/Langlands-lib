# NYLL M353.035: list replacement preserves an absent coefficient

The theorem `Langlands.NYLL.PortInternal.M353.d035` proves the published
proposition `Langlands.NYLL.PortInternal.M353.d035Statement` from
`Replacement.ListStatements`. It is adapted from Naganori Yamaguchi's
private theorem
`LubinTate.SameUniformizer.coeff_replaceList_eq_of_not_mem`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 611–643, at commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`.

The pinned original is readable at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered sources are
`external-lean-reuse-snapshots-2026-10-21` (collection fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The original signature is at lines 611–620 and its proof at lines 621–643.
No matching NYLL erratum was found in the Library's `notes/errata/`.

## Exact scope

The theorem preserves the source's three independent universes and effective
section parameters from lines 29–38: implicit `{K : Type u}`, `[Field K]`,
`{F : LocalField.{u, v} K}`, `{sigma : Type w}` and `[Fintype sigma]`.
These are followed by implicit `L : sigma → F.valuationSubring` and `m : ℕ`,
then explicit `hm : 2 ≤ m`, `target`, `ds`, `H`, `q` and `hq`, in that order.
Here `ds` is a list of exponent vectors of total degree `m`,
`H : d002 (F := F) L` is an actual power series with the prescribed linear
term, `q` is another degree-`m` exponent and `hq : q ∉ ds`.
The conclusion is exactly
`MvPowerSeries.coeff q.1 (d031 hm target ds H).1 =
MvPowerSeries.coeff q.1 H.1`.

The arbitrary target series needs no prescribed-linear-term hypothesis.
Repetitions in `ds` are allowed: the theorem has no nodup assumption.
The unused source section parameter `pi` does not occur in the declaration;
there is no uniformizer witness or `LubinTateSeries` parameter.
The imported `d031` is the actual left fold of the coefficient replacement
step `d030`. The target and its imported Lean/Markdown pairs are unchanged.

## Implemented proof

The initial `change` unfolds the Statement application to its coefficient
equality. Induction on `ds`, generalizing `H`, then follows the original proof.
The empty list gives a reflexive equality. For a head `d` and tail `ds`,
nonmembership gives both `q ≠ d` and `q ∉ ds`. Unfolding the left fold at
the head is definitional. The induction hypothesis identifies the coefficient
after processing the tail with that of the updated accumulator
`d030 hm target H d`. The one-step theorem
`Langlands.NYLL.PortInternal.M353.d033` then identifies that coefficient with
the coefficient of the original `H`, since `q ≠ d`.

The focused imports are `Replacement.ListStatements` for the fixed target
and `Replacement.StepOtherProof` for the exact one-step coefficient law.
The latter adapts the source helper
`coeff_replacementStep_eq_of_ne` at lines 566–578. This proof adds no
mathematical assumption or new definition.

## Adaptations, preparation and license

Worker 294 prepared the source-adapted proof in revision 2 of the public draft
for Task 6116. That preparation qualified the namespaces, renamed the
source-private declarations `Approximation`, `replacementStep`, `replaceList`
and `coeff_replacementStep_eq_of_ne` to `d002`, `d030`, `d031` and `d033`,
and replaced the theorem conclusion by the exact Statement application with
an initial `change`. The mathematical induction follows the original source.
Focused published imports replace the original broad recursive-module imports.

Worker 662 reused that proof, compared its signature and body with the pinned
original and the fixed Library target, expanded this source and attribution
record, and prepared the exact proof successor for independent review.
Worker 294 is credited as coauthor for the reused preparation. These preparation
credits do not replace Naganori Yamaguchi's original authorship.

The original 2026 copyright, Apache-2.0 release and author header are retained
verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
