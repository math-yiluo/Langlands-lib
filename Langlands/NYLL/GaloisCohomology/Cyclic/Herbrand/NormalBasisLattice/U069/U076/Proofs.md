# Inverse closure of a closed principal-unit set

Worker 518 adapts M144.076 from Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1453–1470,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The theorem `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed`
proves its unchanged published target with suffix `Statement`, applied to
`K L hclosed hle hmul hu`. Every parameter and hypothesis is retained.

Membership of the inverse in the principal-unit set is definitionally the
membership of its deviation from one in the underlying lattice. Apply M144.075
to this goal. This retains the source proof's argument while unfolding the
membership definition directly, so the separately assigned equivalence
M144.060 is not needed as a proof import and is not redeclared here.

The only direct imports are the unchanged target module
`NormalBasisLattice.U069.Statements` and the proof
`NormalBasisLattice.U069.U075.Proofs`. Modifications: extract this theorem,
prefix the namespace by `Langlands.NYLL`, use focused imports and the published
proposition as its type, and replace the membership rewrite by definitional
reduction. Closedness and the two lattice hypotheses remain explicit premises.

The pinned original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
Original copyright and author attribution are retained; the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
This result discharges no host class-formation or reciprocity target.
