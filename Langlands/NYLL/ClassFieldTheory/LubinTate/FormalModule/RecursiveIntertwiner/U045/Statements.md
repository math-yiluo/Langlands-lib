# M353.045: equality with a prescribed linear term

Worker 356 extracted the exact proposition target
`Langlands.NYLL.LubinTate.SameUniformizer.eq_of_hasLinearTerm_of_intertwinesStatement`
from Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`,
lines 1002–1015 (signature and conclusion: 1004–1011).
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The individual Lean source file SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.

The target retains three independent universes, with `{K : Type u}`,
`[Field K]`, `{F : LocalField.{u, v} K}`, `{pi : F.valuationSubring}`,
`{sigma : Type w}` and `[Fintype sigma]`. It uses the published shared
`LocalField` extending `CompleteDVF`, its actual valuation subring, and the
shared `LubinTateSeries F pi` structure.

Its explicit parameters and hypotheses, in source order, are:

1. `hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K)`;
2. `e ebar : LubinTateSeries F pi`;
3. `L : sigma → F.valuationSubring`;
4. implicit `H H' : MvPowerSeries sigma F.valuationSubring`;
5. `hH : HasLinearTerm H L`, then `hI : Intertwines e ebar H`;
6. `hH' : HasLinearTerm H' L`, then `hI' : Intertwines e ebar H'`.

The conclusion is exactly `H = H'`. The published `HasLinearTerm` means
that the difference from `linearForm L` has total order at least two.
The published `Intertwines` is the literal formal substitution equation
between `e`, `ebar` and the specified series. Both hypotheses are retained
for each series. The uniformizer hypothesis is retained even though its
proof is unnecessary for forming the equality proposition.

The adaptations are the namespace prefix `Langlands.NYLL`, the suffix
`Statement`, conversion of the source theorem into a reducible
Prop-valued `abbrev`, replacement of the source module imports by the
published `LinearTerm.Definitions` and `Intertwiner.Definitions`, and
documentation of this focused unit. A local unused-variable linter setting
preserves every source hypothesis name. No definitions or instances are
introduced besides the proposition target.

The target itself needs only these two published definition modules;
M353.044 and the recursive-series construction are proof dependencies of
the source's equality argument. The focused declaration check of this
module tests that import reduction. This statement does not claim a
published proof; the exact proof is a separate successor after target
publication. M353.046, `existsUnique_intertwiner`, is outside this unit.

The original copyright, Apache-2.0 license and author header are retained.
The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged. This source module has no patch10 edits.
No applicable entry was found in `notes/errata/`.
