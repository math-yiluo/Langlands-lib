# Conditional connectedness constancy for split generic fibres

Worker 105. This internal reduction completes the incidence-chain assembly for
an already split generic fibre. It explicitly assumes both
`FiniteTypeGeometricallyIrreducibleGenericSpreading` and
`FiniteClosedGeometricallyConnectedCoverCriterion`. It proves neither input.

The source motivation is the final paragraph of the proof of Stacks Project
Lemma 37.28.4 (055G), registered collection
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
retained `055C.html`. This implementation uses the existing Noetherian
closure-cover and incidence construction in place of the source's generic
flatness shrinking. The Noetherian hypothesis is retained. This is a
conditional split-fibre reduction, not the unrestricted source theorem.

`GeometricallyConnectedFiberConstancyAt f η` means that there is an open
neighbourhood of the actual point `η` such that each actual residue-field
fibre over that neighbourhood is geometrically connected if and only if
the fibre over `η` is. The definition imposes no finiteness or generic-point
hypothesis. Geometric connectedness includes nonemptiness.

The first helper applies the assumed closed-cover criterion over the actual
residue field. Its covering maps are the actual pullback closed immersions
into the fibre. Their ranges are identified with `fiberSubschemeSets` by
the existing range comparison.

For a finite closed cover of the generic fibre whose reduced induced schemes
are geometrically irreducible, the earlier conditional spreading construction
gives an open containing the generic point. On this open the actual closure
pieces cover each fibre, remain geometrically irreducible and have exactly
the generic cover's pairwise intersection pattern. Geometric irreducibility
implies geometric connectedness. The assumed closed-cover criterion therefore
identifies geometric connectedness of each fibre with connectedness of its
incidence chains. `intersectionChainConnected_congr` compares the chains at
an arbitrary point and at the generic point through their common pattern.
The resulting equivalence proves Boolean constancy, including when the
generic fibre is disconnected or empty.

The final theorem uses all actual maximal irreducible components of the
generic fibre and assumes `FiberComponentsGeometricallyIrreducible`. A
finite-type scheme over a field is Noetherian, so those components form a
finite index type; their actual closed subsets cover the generic fibre.
The general cover has an independent index universe `v`; actual components
use the scheme universe `u`.

Both assembly theorems retain a Noetherian base and a locally finite-type,
quasi-compact morphism. They require no reducedness, flatness, properness,
smoothness, separatedness or quasi-separatedness. Finite étale splitting,
unconditional geometric-irreducibility spreading, the closed-cover criterion,
generic constancy without the split-component assumption and geometric-fibre
constructibility remain separate proof obligations.
