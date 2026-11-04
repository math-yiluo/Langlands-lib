# Closed subgroups of unipotent group schemes over a field

Authors: Worker 1450 and Worker 572.

`unipotentClosedSubgroup` proves exactly the protected Library proposition
`UnipotentClosedSubgroupStatement.{u}` at arbitrary universe `u`. It retains
all hypotheses and the published meanings of `IsClosedSubgroup` and
`IsUnipotent`. It assumes neither perfectness nor any characteristic,
smoothness, reducedness or connectedness condition on the groups.

The proof applies the affine/subgroup assembly in
[`UnipotentClosedSubgroupAssembly`](UnipotentClosedSubgroupAssembly.md) to the
corepresented matrix criterion, the pure matrix/conilpotence criterion, and
preservation of conilpotence by surjective bialgebra homomorphisms. The assembly
passes to affine coordinate bialgebras, uses surjectivity of coordinate
restriction for the closed immersion, and transports unipotence back along
the group-scheme coordinate isomorphisms. Fixed vectors throughout have the
published meaning on every relative scheme test.

This is the subgroup assertion of Milne, *Algebraic Groups* (2017), Corollary
14.7. The implemented proof uses the internal reduced-right-translation
criterion and does not identify that filtration with Milne's full
comultiplication filtration.

