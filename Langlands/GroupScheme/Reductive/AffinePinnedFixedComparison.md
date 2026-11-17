# Pinned comparisons with a fixed based full root-datum equivalence

Worker 591. This internal construction fixes the entire based root-datum
equivalence in comparisons of supplied affine pinned models over arbitrary
common test schemes. It prepares the gluing step for Task 6490; it does not
assert existence or uniqueness of pinned isomorphisms.

For affine pinned models `M` and `N`, supply an equivalence from the full
root datum of `N` to that of `M`, and a proof that it matches their chosen
bases. `fixedTorusIso` is the actual torus isomorphism whose character map
is precisely that fixed equivalence's weight map, including all central
lattice directions. `fixedSimpleEquiv` restricts its root-index equivalence
to the chosen simple roots.

`PreservesFixedTorus` is the specified torus-square identity.
`PreservesFixedPinning` tests the actual simple dual-number vector points
on every affine coefficient test, using precisely the supplied fixed
simple-root correspondence. The coefficient rings need not be local, and
the original model rings and coordinate types may differ. `FixedComparison`
is an actual group-scheme comparison together with these two properties.

The fixed torus isomorphisms commute with arbitrary base change by the
published exponent-torus construction. The prescribed torus square then
pulls back through the actual direct/iterated group and torus comparisons.
Each fixed pinning-vector equation pulls back using the published
root-vector-point comparison theorem. `FixedComparison.pull` and
`pullAlong` implement these operations, including explicitly equal
endpoint maps. The final two lemmas recover ordinary torus preservation
and the Library's weaker local pinning predicate from the fixed data.

These definitions deliberately retain the fixed based root-datum map;
allowing a new simple-root relabelling on every test would not supply the
uniqueness needed for gluing. Their provenance is an internal refinement
of the imported actual comparison and pinning-point constructions,
in the setting of Conrad, *Reductive group schemes* (2014), Theorem 6.1.17
and Proposition 6.2.11(2). Existence, rigidity, and independent local
comparisons needed for global gluing remain separate obligations.
