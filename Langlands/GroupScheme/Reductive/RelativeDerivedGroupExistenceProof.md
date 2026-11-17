# Existence of the relative derived subgroup with torus quotient

The theorem `Langlands.GroupScheme.relativeDerivedGroupExistence.{u}` proves
exactly the unchanged published `RelativeDerivedGroupExistenceStatement.{u}`.
For every scheme `S` and reductive group scheme `G` over `S`, it constructs
a group scheme `D` and a homomorphism `d : D ⟶ G` satisfying the published
predicate `RelativeDerived.IsAdmissible d`. Thus `d` is a closed subgroup
with normal all-test range, `D` is reductive with semisimple geometric
fibres, and its represented fppf quotient has a relative torus target.
There is no additional hypothesis on the base, characteristic, splitness,
reducedness, noetherianity or quasi-compactness. The proof is uniform in
the universe.

The implemented proof composes the actual quotient construction with
relative semisimple fppf-perfectness. The local construction parametrizes
actual root subgroups, isolates the opposite pair of a simple root by a
simple-wall cocharacter, and extracts a literal rank-one relation from a
full cell relation. Actual rank-one Weyl data on a faithful etale cover
prove that the coroot quotient preserves the original torus coordinate.
An injective generic deformation removes the denominator-unit condition,
retaining nilpotent scheme information. The negative-simple, positive-root
and torus generator laws then glue the coroot cell projection to an
actual smooth surjective local quotient with the prescribed torus
restriction.

The canonical dynamic-cell assembly applies the constructed local
witnesses to all local-ring tests of an affine pinned model, proving
compatibility of its predetermined cell formula over every coefficient
ring. It glues the actual arbitrary-ring quotient and proves smoothness
and surjectivity. The full geometric-kernel comparison identifies every
such kernel with the actual field derived subgroup and proves its
semisimplicity. The affine pinned atlas and admissible-subgroup descent
then give the arbitrary-scheme construction. The separate unconditional
`relativeSemisimpleFppfPerfect` theorem supplies the fppf-local abstract
commutator generation needed in that descent.

The Lean proof applies
`relativeDerivedGroupExistence_of_relativeSemisimpleFppfPerfect` to
`relativeSemisimpleFppfPerfect`. The former theorem already discharges the
local and split quotient construction inputs. Consequently the final
theorem retains no mathematical premise beyond the unchanged target's
reductivity assumption. It does not assume the parent relative
derived-group existence-and-uniqueness theorem. Its provenance is this
internal composition of the stated construction and perfectness proofs;
the target statement and its imported Lean/Markdown pairs are unchanged.
