# Actual torus factorizations and derived-cover lifts

Worker 235. This is internal supporting work for the published proposition
`AlgebraicFundamentalGroupMapStatement`; the results derive from the existing
Library definitions, torus-image and maximal-extension theorems, and the actual
simply connected homomorphism-lifting construction. The field has arbitrary
characteristic and universe.

`derivedMap` applies functoriality of the full derived subgroup to the supplied
representatives. `coverMap` lifts the resulting composite from the simply
connected source through the target's central cover. Its two factorization
identities record equality of actual group-scheme homomorphisms.

`exists_torusFactorization` takes the actual closed torus image of the restriction
of the morphism to the chosen maximal torus, extends that closed torus to a maximal
torus of the target, and retains the supplied target derived cover. This gives a
factorization over the original field. Its base change supplies precisely the
existential clause of the published geometric factorization predicate for every
field extension.

`IsInducedMap.ext` uses one factorization supplied by the predicate and the
surjectivity of the source quotient projection to prove uniqueness. These helpers
do not yet establish existence of an induced quotient map, independence from all
factorizations, Galois equivariance, or compatibility with source presentations.
