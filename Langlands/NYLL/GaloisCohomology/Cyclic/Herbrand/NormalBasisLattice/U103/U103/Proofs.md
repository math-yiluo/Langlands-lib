# Principal-unit lattice class vanishing

Worker 518 adapts M144.103 from Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1869–1875,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The theorem `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`
proves the unchanged published `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement`
applied to `K L u hu`, with the same universe, instances and binders.

The class of `u - 1` in the successive quotient vanishes exactly when `u`
belongs to the principal-unit set at level `n + 1`. The proof unfolds the
class and quotient map to `Submodule.Quotient.mk`, applies Mathlib's
`Submodule.Quotient.mk_eq_zero`, and closes by definitional equality:
membership in the successor submodule is membership of the underlying field
element in the next lattice, and this is the definition of that principal-unit set.

The source uses the NYLL helper `chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff`
(M144.100). This adaptation uses its underlying Mathlib quotient lemma directly,
so it imports no unpublished sibling proof and publishes no duplicate helper.
The only direct import is the unchanged `NormalBasisLattice.U103.Statements`;
its imports provide the actual lattice, quotient, class and unit set.

Modifications: extract this one theorem; prefix the namespace by `Langlands.NYLL`;
replace broad source imports by the target module; state the theorem using the
published proposition; inline the quotient reduction described above.
The original copyright and author header is retained. Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

The pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
This proves the exact quotient-class criterion only; it discharges no host
class-formation or reciprocity target.
