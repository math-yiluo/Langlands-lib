# Factorization of cocycles on finite Galois covers

`Langlands.GroupScheme.Cocycle.FiniteGaloisCocycleFactorizationStatement`
compares point factorizations at the Galois automorphisms with
factorizations on arbitrary tests. Let `ξ` be a cocycle of `G` on
`Spec M` for a finite Galois extension `M/K`. Suppose for every
automorphism `σ` the value at `(1, σ)` factors through a group scheme
homomorphism `j : H ⟶ G`. Then every value on a pair of points of the
cover factors through `j`.

The proof uses the Library's decomposition of the double overlap as the
coproduct of `Spec M` indexed by Galois automorphisms. The local
factorizations glue to a map from that overlap into `H`. Composing
with `j` gives the cocycle's universal value, as can be checked on
each component. Pulling back this factorization along a pair of points
gives the claimed factorization on the test. When `j` is a monomorphism,
`Cocycle.lift` can use these factorizations to produce a cocycle of `H`.
