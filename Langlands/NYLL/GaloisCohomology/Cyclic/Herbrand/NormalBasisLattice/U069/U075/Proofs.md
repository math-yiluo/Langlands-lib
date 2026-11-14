# Closedness contains the inverse correction

Worker 518 adapts M144.075 from Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1424–1450,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The theorem `Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed`
proves its unchanged published target with suffix `Statement`, applied to
`K L hclosed hle hmul hu`. Its universe, instances, implicit level and unit,
closedness, maximal-ideal containment, multiplicative closure, and membership
hypotheses are retained.

Set `x` to the field value of `u - 1`. The private helper
`inverseCorrection_limit_mem` uses additive negation and induction on positive
powers to put every `(-x)^(i+1)` in the lattice. Closure under finite sums then
puts each inverse-correction partial sum in it. Apply Mathlib
`IsClosed.mem_of_tendsto` to the limit supplied by M144.073. The limit is the
field value of the inverse unit minus one, which is definitionally the cast
of its integer-ring deviation from one required by the target.

The direct imports are `NormalBasisLattice.U069.Statements` and
`NormalBasisLattice.U069.U073.Proofs`. The private helper inlines the elementary
arguments of source M144.029/M144.036/M144.065 and the closed-limit step of
M144.041; none of those separately assigned source-adapted theorem names is
introduced or needed as a proof import. The helper is internal proof code,
derived from the actual submodule operations and Mathlib's closed-set theorem.
M144.073 is the only additional NYLL proof dependency introduced directly here.

Modifications: extract this target, prefix its namespace by `Langlands.NYLL`,
use focused imports and the published proposition as the type, and inline
the algebraic and closed-limit steps under a private distinct name.

The pinned original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
Original copyright and author attribution are retained; the existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` apply.
This result discharges no host class-formation or reciprocity target.
