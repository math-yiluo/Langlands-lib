# Factoring finite fields through unramified Galois stages

This internal construction packages a consequence of the published finite
Galois unramified exhaustion of the inertia fixed field. It works in the
original universe and retains a specified field embedding.

`FieldFactorization F K a` records a finite Galois arithmetically unramified
intermediate field `E` of the chosen separable closure, containment of `E`
in the inertia fixed field, and an `F`-algebra embedding from `K` to `E`.
Its factorization equation says that composing this embedding with the
actual inclusion of `E` into the inertia fixed field gives exactly `a`.

`nonempty_fieldFactorization` chooses finite algebra generators of `K/F`
and applies `separableUnramified` to their images under `a`. All elements
of `K` then map into the resulting field, by the universal property of
algebraic adjoining. Restricting the codomain gives the specified
embedding, and equality of the underlying elements proves factorization.
`fieldFactorization` chooses this construction. The finite-dimensional
hypothesis is used to obtain the finite algebra generators.

No descent of group schemes or generic-fibre identifications is claimed
by this field construction.
