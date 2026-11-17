# Actual derived-subgroup isomorphisms induced by ambient isomorphisms

Over an arbitrary base scheme, let `d : D ⟶ G` and `e : E ⟶ H` be actual closed
representatives of the full scheme-theoretic derived subgroups. An actual
isomorphism `f : G ≅ H` induces `hd.mapIso he f : D ≅ E`.

This construction has internal provenance. The published
`derivedSubgroup_comap_iso` identifies the full derived subgroup functors under
`f`, on every test scheme. Applying the published `isoOfComap` to their supplied
representatives gives the actual isomorphism. Its forward and inverse inclusion
squares are those of `isoOfComap`.

The forward homomorphism is the existing `IsDerivedSubgroup.map` of `f.hom`:
both maps have the same composite with `e`, so the target representative's
monomorphism makes them equal. The same cancellation proves that any actual
isomorphism with the displayed forward inclusion square equals `mapIso`.
No smoothness, field or characteristic hypothesis is used.
