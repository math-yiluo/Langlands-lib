# Addition of principal-unit lattice classes

Worker 518 adapts M144.106 from Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1942–1967,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The theorem `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add`
proves the unchanged published statement with suffix `Statement`, applied to
`K L hmul_error u v hu hv huv`. It retains every source instance and binder.

Assuming the displayed multiplicative error belongs to the next lattice,
the class of `uv - 1` equals the sum of the classes of `u - 1` and `v - 1`.
The three membership proofs ensure that all representatives lie in the current lattice.
The implemented proof unfolds the three classes and uses linearity (`map_add`)
to express the sum as the image of the sum of representatives. Mathlib's
`Submodule.Quotient.eq` reduces equality of these quotient classes to membership
of their difference in the successor submodule. By the definitions of the
successor submodule and subtype arithmetic, this is exactly the supplied
`hmul_error u hu v hv`.

The original proof uses NYLL's quotient equality and successor-membership
helpers (M144.101 and M144.091). This adaptation applies the underlying Mathlib
quotient equality theorem and definitional reduction directly; it neither
imports unpublished sibling proofs nor introduces duplicate helper declarations.
Its only direct import is the unchanged target module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.Statements`.

Modifications: extract this one theorem, prefix the namespace with `Langlands.NYLL`,
replace broad source imports with the target import, give the theorem the published
proposition as its type, and inline the quotient reduction described above.
The original copyright and author header is retained; Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.

The pinned original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
The result is conditional on the stated error hypothesis; it discharges no host
class-formation or reciprocity target.
