# NYLL M353.041–042: coefficient agreement and degreewise defect response

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

The prerequisites are published in the Library: the sibling `ReplaceDegree`
data pair containing d040, the approximation subtype d002, replacement data
d030/d031 and degree-index list d003. These targets use the actual published
imports. This pair states the coefficient laws; it contains no proofs of them.

## Source correspondence

| Unit | Source private theorem, signature lines | Target |
| --- | --- | --- |
| M353.041 | coeff_replaceDegree_eq_target_of_degree_le, 847–857 | Langlands.NYLL.PortInternal.M353.d041Statement |
| M353.042 | coeff_defect_replaceDegree, 873–885 | Langlands.NYLL.PortInternal.M353.d042Statement |

Source proofs occupy 858–871 and 886–891. The source section parameters
are at lines 29 and 34–38.

## Meaning and full hypotheses

Both targets use a field K, the shared local field F, a variable type sigma
with Fintype, implicit prescribed linear coefficients L, an arbitrary series
target, H : d002 (F := F) L, and explicit m : ℕ with hm : 2 ≤ m. The
three universe parameters u, v, w remain independent. All implicit/explicit
binder kinds and source order are retained inside the closed propositions.

The .041 target assumes exactly hlower : ∀ q, q.degree < m →
coeff q H.1 = coeff q target and, for the queried exponent q, hq :
q.degree ≤ m. It concludes coeff q (d040 target H m hm).1 = coeff q target.
In particular hlower covers every degree strictly below m, not just a
smaller truncation. There is no pi, uniformizer proof, e or ebar parameter.

The .042 target additionally has implicit pi and explicit
(e ebar : LubinTateSeries F pi) before L, exactly as in the source; it
requires hq : q.degree = m, not a bound. Its conclusion is that the new
defect coefficient at q equals its old value plus
pi * ((1 - pi ^ (m - 1)) * (coeff q target - coeff q H.1)).
It assumes neither hlower nor a uniformizer proof.

Neither target requires target to have the prescribed linear term. They
import d040 data and the shared defect definition; degree-list and
replacement-law proofs are reserved for the exact proof successors.

## Adaptation and attribution

Worker 325 extracted these units on 14 November 2026, qualified references
with `Langlands.NYLL`, assigned the task's public `PortInternal.M353` names
to source-private declarations, and replaced broad source imports by focused
Library modules. Statements quantify the complete effective source telescope
inside a closed Prop definition and omit source proofs. Data retain their
source bodies with adapted dependency names. Universe and binder kinds are
preserved. The unused-variable linter is disabled locally in these target
modules to retain the original hypothesis names inside the closed propositions. No global instances or patch10 changes are introduced.

The shared LocalField extends the published CompleteDVF, and the shared
LubinTateSeries interface is used wherever it occurs in the source.
Approximation is d002, replacementStep is d030, replaceList is d031, and
degreeIndexList is d003. These are source-name adaptations, not new
mathematical constructions. The original copyright, Apache-2.0 release and
author header are preserved verbatim. Existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.
