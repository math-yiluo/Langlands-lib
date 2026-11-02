# Zariski gluing of general relative rigidified classes

This internal generalization of the published abelian-scheme Zariski gluing
construction uses arbitrary schemes `S`, `X`, a map `f`, a section `ε` and
its section law. It assumes that isomorphisms between all relative rigidified
line bundles are unique. The final theorem `classes_zariskiGluing_of_unique`
glues classes on any open cover of a test scheme when their actual pullbacks
to the pairwise base overlaps agree. The global class pulls back to the
given class on every member of the cover.

The construction transports chosen overlap isomorphisms from relative spaces
of base overlaps to overlaps of the induced total-space cover. The analogous
identification on triple overlaps transports uniqueness of rigidified
isomorphisms to those spaces. Uniqueness then proves the module cocycle
condition. The published module gluing theorem constructs a module with the
chosen local identifications, and local rank one follows from those charts.

The local rigidifications are transported through the chart identifications.
The imported comparison lemmas and the compatibility of the module charts
show that they agree on base overlaps. The published isomorphism gluing
theorem on the base then constructs the global rigidification. Each chart
identification preserves that rigidification. Quotient soundness gives the
claimed equality of actual classes.

The helpers `overlapIso`, `overlapSection`, `tripleIso`, `tripleSection` and
`isoTransport` describe the actual schemes, sections and transported
isomorphisms used above. `rigidifiedIso_subsingleton_of_iso` transports the
explicit uniqueness input to an identified relative space. `exists_glued`
is the step using that input for the cocycle. `exists_rigidification` and
`glued_restrict_iso` supply the global rigidification and its local checks.
`classes_zariskiGluing_of_unique_of_moduleGluing` exposes the module gluing
input; the final theorem supplies the published module gluing result.

This is derived internal content obtained by generalizing
`RigidifiedClassesZariskiGluingProof` and reusing its generic module and
rigidified comparison lemmas, together with the relative cover constructed in
`RigidifiedClassesZariskiSeparatedGeneral`. The abelian-scheme uniqueness
result is replaced by precisely the relative uniqueness hypothesis used in
the construction. This module does not prove that hypothesis. It establishes
Zariski existence of a glued class; the corresponding separation helper is
available in the imported module. No fppf descent or final comparison theorem
is asserted here.
