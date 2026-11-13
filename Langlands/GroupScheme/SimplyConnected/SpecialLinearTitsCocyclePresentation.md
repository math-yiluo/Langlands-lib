# A coordinate special-linear presentation over a finite Galois cover

This internal construction combines the stronger finite-stage comparison with
the coordinate pinned-isomorphism construction. It retains the actual Tits
index supplied by the caller. It does not establish the discrepancy matrix or
torus weight conclusions of `SpecialLinearTitsCocycleStatement`.

`Presentation d e` contains a finite Galois extension `L/K`, an embedding into the
separable closure, finite-stage Galois pinning data, and an actual isomorphism of
its original torus with the original torus in `d.pinning`. Its inclusion equation
identifies their actual group-scheme inclusions. The full root-datum equivalence
uses precisely the tower character map after this torus identification; it
preserves the supplied bases and intertwines the star actions of every pair of
compatible field automorphisms. The final field is a `CoordinatePinnedIso` to
that finite-stage pinning with the numbering transported from the given `e`.

`Presentation.numbering` exposes that transported numbering.
`Presentation.baseChangeIso` composes the actual special-linear base-change
model comparison with the coordinate pinned group isomorphism.
`Presentation.localIso` uses `LocalGroupIso.ofBaseChangeIso` to obtain an actual
natural local group isomorphism on every test scheme. `Presentation.star_vertex`
expresses the retained root-datum star comparison on the actual simple vertices.
`Presentation.localIso_toBaseChangeIso` identifies its recovered base-change
isomorphism with the defining composite, and
`Presentation.localIso_toBaseChangeIso_hom` exposes that equality on forward
group-scheme morphisms.

`exists_presentation` constructs the data for a simply connected group whose
supplied Tits Cartan pairings have type `A_n` under `e`. It first uses
`StarActionFiniteStage.exists_finiteGaloisStage_torus`, transports the numbering
through its base-preserving root-datum equivalence, and transports the Cartan
pairings through that equivalence. Simple connectedness ascends to `L` by
`isSimplyConnectedFieldExtension`; hence `exists_coordinatePinnedIso` constructs
the required coordinate pinning and pinned isomorphism. No assumption of
absolute almost simplicity is needed for this partial construction.

All fields, characteristics and ranks, including zero and one, are retained.
This is a derived composition of the named interfaces, without new external
mathematical input or a downstream classification premise.
