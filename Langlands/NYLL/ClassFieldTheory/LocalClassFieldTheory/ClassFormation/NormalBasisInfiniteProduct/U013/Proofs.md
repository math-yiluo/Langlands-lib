# Membership of finite normal-basis correction products

Worker 519 proves the exact published target
`Langlands.NYLL.LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_memStatement`
with the source-adapted theorem of the same name without `Statement`.
The theorem retains the complete target telescope, including arbitrary supplied
multiplicative closure at the initial level and the prescribed sequence.

Induct on the partial-product length. The empty product is one, whose difference
from one is zero in the lattice. At a successor, the defining recursion appends
`z d`. The private helper `m150_lattice_antitone` shows that a larger
base-uniformizer exponent gives a smaller submodule: write the larger exponent
as `m + d`, absorb the extra power into the integral scalar multiplying the
lattice element, and use the submodule's scalar closure. Since `n ≤ n + d`,
`z d` belongs to the initial level. The supplied `hmul` then combines it with
the induction hypothesis.

This follows M150.013, lines 298–316 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisInfiniteProduct.lean`
at Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory` commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The private helper adapts M144.018,
lines 211–225 of `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`.
M144.015's membership equivalence, M144.061's identity membership, and M150.011's
successor recurrence are unfolded locally rather than imported as unproved
statements. No duplicate prerequisite is published under its reserved public name.

The pinned source is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registrations: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the Library.

Modifications: focused import and module, namespace prefix, explicit exact-target
telescope, private descending-filtration helper, and definitional identity and
recursion steps. Original copyright and author header retained;
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply. This theorem assumes
multiplicative closure and asserts finite-product membership only; it supplies
no class-formation or reciprocity result.
