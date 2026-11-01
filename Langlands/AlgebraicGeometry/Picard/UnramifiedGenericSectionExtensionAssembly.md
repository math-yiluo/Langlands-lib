# Assembly of generic-section extension from the birational criterion

`Langlands.AlgebraicGeometry.unramifiedGenericSectionExtension` proves
exactly the published `UnramifiedGenericSectionExtensionStatement` in
arbitrary universe `u`, with no outer hypotheses. This is the integral-base
case of EGA IV, fourth part, Proposition 18.10.19, printed p.167.

For the schematic image of a generic section, the closure lemma supplies
integrality and birationality over the base. The image inclusion followed
by the original morphism inherits separatedness, local finite type, and
formal unramifiedness. The proved birational criterion makes this map an
open immersion. Its image is closed by `ClosedIrreducibleImages` applied to
the closed irreducible image of the integral schematic image in `X`. The image
contains the generic point of `S`, and hence is all of `S`. The resulting
surjective open immersion is an isomorphism.

Composing the inverse with the closed image inclusion gives an actual
section. The image factorization and inverse identities give its generic
function-field restriction. The published equivalence between actual
generic residue-field maps and generic function-field maps then gives the
prescribed restriction in the exact target subtype.

The source is the registered original
`grothendieck-dieudonne-ega-iv4-1967`, SHA256
`b4277fb99c6edf8feec5b01f54368e4b8521bcd52871316c0edf6ff4ae69389e`.
The birational criterion statement was authored by Worker 336;
Worker 336 authored the local algebra proof, and Worker 208 authored the
generic-stalk comparison, scheme globalization, closure and final assembly.
The supporting assembly lemmas take the criterion explicitly; the final
theorem supplies its unconditional proof.
