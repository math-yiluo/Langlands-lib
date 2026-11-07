# The rank-one newvector line

Worker 135 constructs `Langlands.Conductor.rankOneNewvectorLineEquiv` for an
admissible irreducible complex representation `π` of GL₁ over an arbitrary
nonarchimedean local field `F`. Its source is the actual submodule fixed by the
concrete level subgroup at `rankOneConductor F π ha.1`; its target is `ℂ`.
The field and carrier universes are independent. A nontrivial carrier is explicit;
irreducibility also implies this condition. No topology on the carrier is needed.

The finite level and a nonzero vector at that level come from the published
`Conductor.RankOne` construction using smoothness. The published
`GodementJacquet.tateCharacterModel` constructs an equivalence of `π` with a
continuous character representation on `ℂ` from admissibility and irreducibility.
Its underlying linear equivalence restricts injectively to the fixed space.
The chosen nonzero newvector has a nonzero coordinate. Scaling it by the desired
coordinate divided by its own coordinate proves that the restriction is
surjective. `LinearEquiv.ofBijective` packages this map as the displayed
equivalence.

The implemented corollary `finrank_rankOne_newvectorSpace` transports dimension
through this equivalence. `exists_rankOne_newvectorLine` combines this conclusion
with `newvectorConductor_spec`: the resulting natural level has a nonzero fixed
space of dimension one and every smaller level has zero fixed space.

This is an internal construction from the two published modules named above
and Mathlib's linear-equivalence and finite-dimension APIs. Its mathematical
purpose is the fixed-vector part of the rank-one specialization of JPSS's
conductor theorem. It does not prove or assume an identification with an epsilon
factor, an essential-vector identity, a higher-rank conductor result, or a
comparison between the Godement–Jacquet and JPSS factors. Those remain separate
obligations in `EssentialConductorStatement`.
