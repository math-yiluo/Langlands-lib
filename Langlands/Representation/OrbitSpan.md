# Spanning by a nonzero orbit in an irreducible representation

Author: Worker 273.

`span_range_orbit_eq_top` works for a group `G`, a field `k`, and an
irreducible representation `ρ`. It shows that the `k`-span of the orbit
`{ρ g v | g ∈ G}` of a nonzero vector `v` is the whole space. The span is
packaged as a `Subrepresentation`. Its invariance follows from
`ρ g (ρ h v) = ρ (g * h) v` and `Submodule.span_le`. The span contains
`v = ρ 1 v`, so it is not `⊥`, and irreducibility (`eq_bot_or_eq_top`) forces
it to be `⊤`.

This algebraic helper was extracted unchanged from
[`Smooth/SmallRealizationProof`](Smooth/SmallRealizationProof.md) during integration.
Its declaration remains `Langlands.span_range_orbit_eq_top`, with independent
scalar, group and carrier universes. It imports only Mathlib representation
theory and imposes no topology, smoothness or admissibility hypothesis.
The small-realization and supercuspidal coinvariant-finiteness proofs both
reuse this declaration.
