# Parallel isomorphisms and automorphisms on a complete slice

This internal categorical construction supplies the isomorphism-torsor
comparison used for the actual Picard endpoint kernel. `pullIso_trans`
proves that coherent isomorphism pullback preserves composition; its proof
expands the composition comparisons and cancels the shared middle one.
`pullIso_congr` replaces an equal restricting map while keeping its two
endpoint maps fixed, with proof irrelevance supplying the triangle witnesses.

For fixed morphisms `a,b : T → U` and an actual family `ξ` over `U`,
`parallelIsoPresheaf` retains all isomorphisms between its pullbacks along
`q ≫ a` and `q ≫ b` for every `q` over `T`. Restriction uses coherent
pullback along every morphism in the full slice, and its functor laws are
the identity and composition laws already proved for `pullIso`.

Given an actual isomorphism `e` over `T` between these two pullbacks,
`automorphismParallelIso` is an isomorphism from the source automorphism
presheaf pulled back along `a` to this entire presheaf of parallel
isomorphisms. On a test `q` it postcomposes an automorphism with the
coherent restriction of `e`; its inverse postcomposes with that
isomorphism's inverse. The inverse laws are the ordinary isomorphism
identities. Naturality uses composition preservation and the composition
law of coherent pullback together with the slice triangle for `q`.
No global arrow is chosen without the given `e`, and no geometric
representability or quotient assertion is made in this construction.
