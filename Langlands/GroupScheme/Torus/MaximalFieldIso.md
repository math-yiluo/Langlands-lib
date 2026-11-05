# Maximal tori under field isomorphisms

This internal construction assembles the actual group-scheme pullback
composition and identity comparisons into `baseChangeSectionComparisonNatIso`. A base
map followed by a section therefore gives a natural isomorphism from the two
successive pullback functors to the identity. Its components are the existing
`baseChangeSectionIso`. The shared
`RadicalFieldTransport.sectionIso_naturality` gives the exact recovery equation
for each original group homomorphism. The differently associated construction
`baseChangeSectionNatIso` in `Absolute/ParabolicBorelFactorization` retains its
existing name and definition.

`IsMaximalTorus.baseChange_fieldIso` preserves maximality under any isomorphism
of fields in an arbitrary common universe. Pull back the inclusion along the
field isomorphism and then its inverse. Naturality identifies this double
pullback with the original inclusion through source and ambient isomorphisms.
The existing maximality transport lemmas give maximality of the double
pullback. The independent `IsMaximalTorus.of_baseChange` then reflects it from
the inverse field extension. Closedness needed by reflection is ordinary
base change of the original closed immersion.

The result has no finiteness, characteristic, smoothness, connectedness,
splitness, or reductivity hypothesis. This argument does not use general
forward preservation of maximal tori under field extension or any
no-torus/unipotence theorem. It only treats isomorphisms of fields and leaves
maximal-torus existence and conjugacy as separate obligations. Its provenance
is the formal naturality of the published actual pullback comparisons and
the published independent reflection theorem.
