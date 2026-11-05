# Torus centralizers from containment in a solvable subgroup

This internal construction retains `DynamicCentralizerReductiveStatement`
as an explicit premise. For a connected reductive group over any field,
the whole centralizer of any split-torus homomorphism has a closed torus
representative whenever that centralizer lies in a supplied solvable
closed subgroup. No maximality assumption on the split torus is needed
for this assertion.

The proof chooses the published `centralizingCocharacter`, whose dynamic
centralizer equals the original split-torus centralizer on every test
scheme. The displayed dynamic reductivity premise therefore proves
connected reductivity of a supplied closed centralizer representative.
Containment in the solvable subgroup gives a monomorphism into that
subgroup and hence solvability. The unconditional theorem
`IsConnectedReductive.isTorus_of_isSolvableGroupScheme` then gives the
torus property.

`TorusCentralizerTorusData` records an actual commutative group scheme,
its inclusion, its torus and closedness properties, and its representation
of the full centralizer. The noncomputable definition
`torusCentralizerTorusDataOfSolvableContainment` chooses a closed
representative using `fieldCentralizerRepresentability`, proves it a torus
by the preceding argument, and equips it with the resulting commutative
structure.

The geometric Borel specialization uses the adapted maximal split torus
construction with an explicit `ParabolicDynamicStatement` premise. Its
whole centralizer lies in that Borel, which is solvable, so the construction
above applies. Extracting a geometric Borel from `IsQuasiSplit` therefore
gives one maximal split torus with a closed torus centralizer in each
quasi-split group. Both structural premises remain explicit throughout;
neither is proved here.

The implementation uses the stronger published cocharacter construction
for arbitrary split-torus maps, rather than requiring a generic cocharacter
of an ambient maximal split torus. All schemes and maps are over the
original arbitrary field, at arbitrary universe, and all subgroup
comparisons concern the full functors. This module does not establish the
unconditional quasi-split maximal torus centralizer target.
