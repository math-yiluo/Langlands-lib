# Quadratic cocycles with a strongly regular Galois value

`Langlands.GroupScheme.GaloisCocycleStronglyRegularValueStatement` concerns
a connected reductive group `G` over a field `K` of characteristic zero.
Let `M/K` be finite Galois with `M` algebraically closed. Given a cocycle
of `G` on `Spec M` and a nonidentity coefficient automorphism `σ`, the
statement asks for a cochain on the same cover. The value of the twisted
cocycle on `(1, σ)` must have a maximal torus of `G_M` as its centralizer
on all `M`-scheme tests.

The companion theorem assumes this assertion and proves the local toral
representative assertion for algebraically closed quadratic covers. There are two coefficient
automorphisms. The cocycle identity says that the nonidentity automorphism
sends its value to its inverse. The centralizer descends to a maximal torus
over the base field containing this value. The identity value also factors
through the same torus. These two factorizations give a factorization on
every test, from which the proof constructs the desired torus cocycle.
