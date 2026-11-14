# Simply connected derived groups under central surjections

`Langlands.GroupScheme.SimplyConnectedDerivedAscentStatement` asserts that,
over any field `k`, a surjective homomorphism `p : E ⟶ G` between connected
reductive group schemes with central full scheme-theoretic kernel carries the
following implication: if `G` has simply connected derived subgroup, then so
does `E`.

Surjectivity is `AlgebraicGeometry.Surjective p.hom.hom.left` on the underlying
schemes. Centrality is `IsCentral (kernelι p)`, so it applies to the actual
kernel on all test schemes. `HasSimplyConnectedDerivedGroup` means the
existence of an actual derived-subgroup inclusion with simply connected
source. Both connected-reductive assumptions are explicit. The statement
has no restriction on the field's characteristic or perfectness and does
not require that the central kernel be a torus.

This is a derived internal statement for the z-extension common-domination
construction, rather than a transcription of an additional source result.
Its provenance is the published Library theorem
`IsDerivedSubgroup.isCentralIsogeny_map` in
`Langlands.GroupScheme.CentralSurjection.DerivedMap`, together with
`derivedSubgroupRepresentability`, `derivedSubgroupSemisimple`, and the
incoming-central-isogeny criterion defining `IsSimplyConnected`. A central
surjection induces a central isogeny on the actual derived subgroups; if
the target is simply connected, that isogeny is an isomorphism.

This module defines the proposition; its proof is submitted separately.
