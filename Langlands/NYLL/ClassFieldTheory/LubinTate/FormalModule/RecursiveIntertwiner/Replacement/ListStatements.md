# NYLL M353.034–036: coefficients of list replacement

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
The readable pinned source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The registered snapshot collection `external-lean-reuse-snapshots-2026-10-21`
has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` registers the same pinned project.
No applicable NYLL erratum was found in the Library's `notes/errata/`.

## Exact proposition targets

| Unit | Original private theorem | Signature lines | Public target |
| --- | --- | --- | --- |
| M353.034 | `LubinTate.SameUniformizer.coeff_replaceList_eq_of_degree_lt` | 580–588 | `Langlands.NYLL.PortInternal.M353.d034Statement` |
| M353.035 | `LubinTate.SameUniformizer.coeff_replaceList_eq_of_not_mem` | 611–620 | `Langlands.NYLL.PortInternal.M353.d035Statement` |
| M353.036 | `LubinTate.SameUniformizer.coeff_replaceList_eq_target_of_mem` | 645–655 | `Langlands.NYLL.PortInternal.M353.d036Statement` |

All declarations retain the effective source section parameters from
lines 29–38: implicit `{K : Type u} [Field K]`,
`{F : LocalField.{u, v} K}` and `{sigma : Type w} [Fintype sigma]`.
The three universes are independent. The unused source section parameter
`pi` does not occur in these declarations. There is no uniformizer witness
or `LubinTateSeries` parameter. The shared adapted `LocalField` extends the
published `CompleteDVF`; coefficients are in its actual `valuationSubring`.
The imported `d002 L` is exactly the subtype of series `H` satisfying
`HasLinearTerm H L`, where `H - linearForm L` has total order at least two.
The target series is arbitrary and has no prescribed-linear-term hypothesis.

Each target retains implicit `L` and `m`, followed by explicit
`hm : 2 ≤ m`, `target`, `ds : List {d : sigma →₀ ℕ // d.degree = m}`
and `H : d002 L`, in source order. Their remaining arguments and
conclusions are exactly these:

- `d034Statement` takes `q : sigma →₀ ℕ` and `hq : q.degree < m`.
  It states `coeff q (d031 hm target ds H).1 = coeff q H.1`.
  The exponent is unrestricted except for its lower degree; the list
  has no nodup assumption.
- `d035Statement` takes `q : {d : sigma →₀ ℕ // d.degree = m}` and
  `hq : q ∉ ds`. It states
  `coeff q.1 (d031 hm target ds H).1 = coeff q.1 H.1`.
  Repetitions elsewhere in the list are allowed.
- `d036Statement` takes `hds : ds.Nodup`, then the degree-`m` exponent
  `q` and `hq : q ∈ ds`. It states
  `coeff q.1 (d031 hm target ds H).1 = coeff q.1 target`.
  The source nodup hypothesis and its position before `q` are preserved.

The imported `d031` is the actual left fold of the replacement step over
`ds`. These propositions describe, respectively, preservation below the
replacement degree, preservation at an absent exponent, and assignment at
a member of a nodup list. They retain all source hypotheses even where a
proof term is unused in the equality body. They do not prescribe a list
order beyond its existing order or assert that every degree-`m` exponent
belongs to `ds`.

## Adaptations and proof obligations

Worker 294 extracted the source signatures and conclusions, renamed
source-private references to `d002` and `d031`, qualified namespaces, and
replaced the broad source imports by the focused published
`Replacement.Definitions` module. The independent universes and all
implicit and explicit binders remain unchanged. The theorem commands
become Prop-valued Statement abbreviations, with local
`linter.unusedVariables false` wrappers to retain their explicit proof
arguments without unused-variable warnings. Each target is inspected to
return `Prop`.

No coefficient theorem is proved in this pair. The source proof ranges
589–609, 621–643 and 656–684 belong to separate exact proof successors,
whose required names are `Langlands.NYLL.PortInternal.M353.d034`, `.d035`
and `.d036` respectively. The public targets remain fixed during those
proof tasks.

The original 2026 copyright, Apache-2.0 release and author header are
retained verbatim. The existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain unchanged. No patch10 edit affects this source module.
