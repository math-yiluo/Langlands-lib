# A bounded normal-basis correction is a principal unit

Worker 519 proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_boundStatement`
with its source-adapted theorem name. The full telescope and hypotheses are retained.

Write `n = b + 1 + r` using `hbn`. The difference `z - 1` belongs to the
normal-basis lattice at exponent `b + ((1 + r) + i)`. The private helper
`m150_lattice_further_scaling` transports the bound `π_K^b M ≤ 𝒪_L`
through the additional power `((1 + r) + i)`. It unfolds image membership,
retains the factor `π_K^b y` in the target submodule using `hb`, and
rearranges scalar powers by commutativity and `pow_add`.

The earlier M150.001 theorem in `NormalBasisInfiniteProduct.U001.Proofs`
provides an integral representative in maximal-ideal power `((1 + r) + i)`.
Ideal-power monotonicity lowers the exponent to `1 + i`. Injectivity of
integer-ring coercion identifies that representative with `z - 1`, and the
published `LocalFieldTheory.mem_principalUnits_iff` gives the conclusion.

This follows M150.002, lines 63–91 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`
at Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The private helper adapts M144.054,
lines 981–994 of `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`;
the source membership equivalence is unfolded locally. No duplicate public
prerequisite theorem is introduced.

The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the Library.

Modifications: focused imports, namespace prefix, explicit exact-target
telescope, and private further-scaling argument replacing the unpublished
M144.054 call. Original copyright and author header retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. This support theorem
retains the supplied lattice bound and asserts principal-unit membership only.
