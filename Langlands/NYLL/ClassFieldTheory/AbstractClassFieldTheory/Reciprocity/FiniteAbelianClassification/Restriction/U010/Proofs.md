# NYLL M298.010: restriction on quotient representatives

Worker 783, 16 November 2026.

This module proves the published target
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.restriction_mkStatement`
with theorem
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.restriction_mk`.
For an inclusion `h₁₂ : L₁ ≤ L₂` of finite abelian subextensions and
`k : K.toSubgroup`, the restriction sends `L₂.extensionQuotientMk k` to
`L₁.extensionQuotientMk k`.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`,
M298.010, lines 248–259 (theorem at 252); namespace scaffolding at lines
23–34 and local instances at lines 36–46. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. The original copyright,
Apache-2.0 release and authorship header are retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

## Exact scope

The theorem preserves the complete source telescope: implicit `{G : Type u}`,
instances `[Group G] [TopologicalSpace G]`, implicit `{K : ClosedSubgroup G}`,
implicit `{L₁ L₂ : FiniteAbelianSubextension K}`, and explicit
`(h₁₂ : L₁ ≤ L₂) (k : K.toSubgroup)`, in that order. The conclusion is
`restriction_mkStatement h₁₂ k`. There is one unrestricted universe and no
topological-group or class-formation hypothesis.

The published instances `Langlands.NYLL.PortInternal.M298.d001` and
`Langlands.NYLL.PortInternal.M298.d002` are enabled with
`attribute [local instance]` inside `namespace FiniteAbelianSubextension`, as
in the source scope. Neither instance becomes global.

## Implemented proof and modifications

After unfolding the published proposition target, the proof applies the
injectivity of `L₁.extensionQuotientMulEquiv`. It then simplifies the
published `restriction` definition, which transports the raw quotient
restriction through the two quotient comparison equivalences. The remaining
raw representative identity is closed by `rfl`: the named projections and
comparison equivalences reduce to the quotient presentation, and the raw
restriction sends the class of `k` to the class of the same `k` by definition.
This final reflexivity step replaces the source reliance on simplifier
attributes of the quotient-projection and raw-restriction lemmas. Those
published exact theorems have Prop-valued statement wrappers and omit their
source simplifier attributes; no additional theorem imports are needed here.

The source namespace gains the prefix `Langlands.NYLL`; source imports are
replaced by the published target module; unused ambient section variables
and `open KummerTheory` are omitted. The theorem's conclusion uses the
published Prop-valued target, which is unfolded at the start of the proof.
The source `@[simp]` attribute and the proof route are retained. This module
proves only M298.010.

## Verification

The focused module compiled in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` without errors or warnings. A private
complete-declaration check assigns the unapplied constant `@restriction_mk`
to the entire target telescope and also compiles without errors or warnings.
Inspection reports the single universe parameter `u_1` and only the standard
assumptions `propext`, `Classical.choice` and `Quot.sound`. These development
checks do not establish independent acceptance or publication.
