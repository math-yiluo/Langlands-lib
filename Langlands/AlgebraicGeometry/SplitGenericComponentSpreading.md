# Conditional spreading of split generic components

Worker 105. This derived construction implements the closed-cover assembly in
the proof of Stacks Lemma 37.28.4 (055G), using the actual closure constructions.
It explicitly assumes the full geometric-irreducibility spreading proposition
`FiniteTypeGeometricallyIrreducibleGenericSpreading`, the still unproved
Stacks 0559 target. It does not prove that proposition or finite generic
splitting (0551).

The source for the assembly is registered collection
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`,
retained `055C.html`, proof of Lemma 37.28.4 (055G). The spreading input is
registered collection `stacks-generic-geometric-irreducibility-2026-11-04`,
SHA256 `7779fd83e268ecb0b8a0b8783d039fea6de1ccf33ce652f9bf972c9697b02f8c`,
`0559.html`, Lemma 37.27.5. The implementation replaces the source's generic
flatness argument for intersections by the existing Noetherian
cover/incidence shrinking theorem. The result therefore retains a Noetherian
base; it is an internal reduction, not the unrestricted source theorem.

`fiberClosedSubsetClosureFiberMap` is the actual pullback closed immersion of
the closure of a closed generic-fibre subset into another actual
residue-field fibre. The original schemes have arbitrary common universe
`u`; a finite covering family has independent index universe `v`.

The restriction comparison uses the actual cartesian residue-field diagram
of an open restriction. Both residue-field comparison maps are isomorphisms,
so geometric irreducibility of the restricted fibre is geometric
irreducibility of the original fibre. The closure-fibre comparison uses the
actual pullback-pasting isomorphism and its compatibility with the map to
the residue-field spectrum. Geometric irreducibility implies geometric
connectedness: the geometric-irreducibility hypothesis makes every
field-spectrum pullback irreducible, and each such pullback is therefore
connected.

The finite-cover theorem starts with a finite closed cover of the actual
generic fibre, each with geometrically irreducible reduced closed
subscheme structure. Equal-support comparison transfers this property to
the actual generic fibre of each closure. The explicit spreading
hypothesis gives an open for each closure. Their finite intersection with
the existing cover/incidence open gives a neighbourhood of the generic
point where the actual pieces cover, remain geometrically irreducible
over each residue field and have exactly the original intersection
pattern. Empty generic fibres and empty index families are included.

The final theorem specializes to all actual maximal irreducible components
of the generic fibre using `FiberComponentsGeometricallyIrreducible`.
The finite-type fibre over its residue field is Noetherian, so its component
index is finite. The actual components cover that fibre by
`iUnion_componentSets`; their closed subsets and closures are the existing
`fiberComponentClosedSubset` and `fiberComponentClosureι` constructions.
This theorem assumes geometric irreducibility of those components and does
not construct a finite étale splitting cover.

No reducedness, properness, smoothness, flatness, separatedness or
quasi-separatedness is imposed. The morphism is locally of finite type
and quasi-compact, and the base is Noetherian. Finite generic splitting,
unconditional spreading, generic connectedness constancy and the full
Conrad descent theorem remain separate obligations.
