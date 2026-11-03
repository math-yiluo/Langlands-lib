# Repairing an almost-everywhere local compact family

This derived helper isolates the finite-exception step in the planned adelic
Iwasawa proof. It builds on the published abstract
`CoordinateCompactAssembly` lemmas. It does not construct local maximal compact
subgroups, adelic coordinate maps, or a continuous adelic product lift, and it
does not prove `AdelicGroupPoints.ParabolicIwasawaStatement`.

For a dependent family of types, a predicate `good`, a proof that a good member
exists at every index, and an original family `d₀`, `patchFamily` keeps `d₀ i`
when it is good and otherwise chooses a good member from the local existence
hypothesis. `good_patchFamily` proves the repaired family good everywhere.
`patchFamily_eq_of_good` proves exact preservation at each originally good
index. If the original family is good almost everywhere for a filter,
`patchFamily_eventually_eq` proves that the repaired and original families agree
almost everywhere for that same filter. For the cofinite filter, all changes
therefore lie in a finite set. This argument uses classical choice and does not
assert any effective rule for finding the exceptional set.

`IsLocalIwasawaCompact φ K` combines compactness of the subgroup in the given
ambient topology, maximality among all compact overgroups, and the equality
`Set.range φ * K = Set.univ`, with the source factor on the left.
This is a proposition predicate and contains no local existence theorem.

The theorem `exists_compact_maximal_cover_of_ae_local` takes full local
existence at every index and an original subgroup family satisfying this
predicate at all but finitely many indices. It also takes coordinate separation,
continuity of the coordinate projections, compatibility of the source maps,
almost-everywhere membership of every ambient element in the original family,
finite-support lifting in the source, and a continuous product lift for every
family that agrees almost everywhere with the original family.

The proof patches the subgroup family, retaining almost-everywhere equality
with the original one. Intersecting this equality condition with the
almost-everywhere membership condition transfers the latter to the repaired
family. The original lift hypothesis supplies a continuous product lift of the
repaired family. The published coordinate assembly lemmas then prove
compactness, unrestricted maximality, and the exact covering equality for the
coordinate subgroup. No Hausdorffness or topological-group hypothesis is used
beyond the displayed assumptions.

The provenance is internal and derived: the choice and filter argument fills
the finite-exception step between an almost-everywhere family and the already
published coordinate assembly lemmas. Its motivation is Getz–Hahn,
*An Introduction to Automorphic Representations* (2024), Appendix B,
Theorem B.2.5 and its proof, printed pp.543–544, the spreading-out discussion in
Proposition B.3.1, and the separate local compact inputs in B.4, printed
pp.547–548. These abstract lemmas are not additional verbatim claims from that
source. The October 2026 errata contains no correction to Appendix B.

To apply the theorem to actual adelic group points still requires the actual
coordinate and lift constructions, the local existence theorems at every
place, an almost-everywhere compact family, its absorption of actual adelic
points, and uniform integrality sufficient to construct the displayed product
lifts after finite changes. All remain separate obligations. In particular,
the conditional theorem supplies no proof of the local structural inputs.
