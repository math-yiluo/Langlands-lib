# NYLL M353.040: replace one complete total degree

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
Its SHA-256 is
`627cad1b4ca585bb98d54d4dc97a88735e737576155b62e00476e824862983f6`.
The readable source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveIntertwiner.lean`.
It is registered under `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum occurs in the current `notes/errata/`.

This pair imports the published replacement data d030/d031 from
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.Definitions`
and the published degree-index list d003 from
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Definitions`.
The approximation subtype d002 is supplied by these published dependencies.

## Source correspondence and meaning

The sole definition is Langlands.NYLL.PortInternal.M353.d040, adapted from
source private LubinTate.SameUniformizer.replaceDegree, signature and body
lines 839–845, with docstring at 837–838. The source section parameters
are at lines 29 and 34–38.

For the shared LocalField F over a field K and a Fintype variable type
sigma, d040 takes implicit L, an arbitrary series target, a bundled
H : d002 (F := F) L, explicit m : ℕ and hm : 2 ≤ m. It returns another
approximation with the same L. Its body is precisely
d031 hm target (d003 (sigma := sigma) m) H: replaceList applied to the
list of all degree-m exponent indices. There is no constraint on target
and no pi, uniformizer proof, e or ebar parameter. The source's independent
universes u, v, w and effective telescope are retained.

The body consumes only the data d002, d003 and d031. It does not
need the exact proof of M353.039, or any defect law. This is why the unit
is staged separately when its data dependencies are ready. The fact that
it replaces all degree-m coefficients and preserves lower coefficients
is assigned to separate exact proposition targets and proof successors;
this data candidate supplies the definition only.

## Adaptation and attribution

Worker 325 extracted these units on 14 November 2026, qualified references
with `Langlands.NYLL`, assigned the task's public `PortInternal.M353` names
to source-private declarations, and replaced broad source imports by focused
Library modules. Statements quantify the complete effective source telescope
inside a closed Prop definition and omit source proofs. Data retain their
source bodies with adapted dependency names. Universe and binder kinds are
preserved. No global instances or patch10 changes are introduced.

The shared LocalField extends the published CompleteDVF, and the shared
LubinTateSeries interface is used wherever it occurs in the source.
Approximation is d002, replacementStep is d030, replaceList is d031, and
degreeIndexList is d003. These are source-name adaptations, not new
mathematical constructions. The original copyright, Apache-2.0 release and
author header are preserved verbatim. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.
