# NYLL M353.037–039: exact defect response to list replacement

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
and the shared defect definition. The approximation subtype d002 is also
published. No replacement-law proof is needed to state these targets.

## Source correspondence

| Unit | Source private theorem, signature lines | Target |
| --- | --- | --- |
| M353.037 | coeff_defect_replacementStep_eq_of_ne, 686–696 | Langlands.NYLL.PortInternal.M353.d037Statement |
| M353.038 | coeff_defect_replaceList_eq_of_not_mem, 709–720 | Langlands.NYLL.PortInternal.M353.d038Statement |
| M353.039 | coeff_defect_replaceList_of_mem, 749–764 | Langlands.NYLL.PortInternal.M353.d039Statement |

The source proofs occupy 697–707, 721–747 and 765–835 respectively.
The source section parameters are at lines 29 and 34–38.

## Meaning and hypotheses

For a field K, the shared local field F, independent universes u, v, w,
a variable type sigma with Fintype, an arbitrary pi in F.valuationSubring,
and e ebar : LubinTateSeries F pi, these targets describe defect coefficients
of approximations with prescribed linear term L. The degree m satisfies
hm : 2 ≤ m, target is any multivariable power series, and H : d002 L
bundles a series with HasLinearTerm H.1 L. The target series itself need
not have this linear term.

All replacement-list entries and queried indices use the exact subtype
{d : sigma →₀ ℕ // d.degree = m}. The .037 premise is q ≠ d in that
subtype. Its conclusion says a replacement at d leaves the defect
coefficient at q unchanged. The .038 premise is q ∉ ds, without a nodup
assumption, and says the list leaves that defect coefficient unchanged.
The .039 premises include ds.Nodup and q ∈ ds; its exact conclusion is
that the new defect coefficient is its old value plus
pi * ((1 - pi ^ (m - 1)) * (coeff q.1 target - coeff q.1 H.1)).
No target includes a proof that pi is a uniformizer.

The closed targets retain all source implicit and explicit parameters in
source order, including e and ebar, implicit L and m, explicit hm, target,
ds where present, H, nodup premise where present, subtype indices and the
member/nonmember/inequality premise. The statements import only the
replacement data and defect definitions; monomial-response and prior
replacement-law proofs are needed by later proof tasks, not by these
signatures.

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
