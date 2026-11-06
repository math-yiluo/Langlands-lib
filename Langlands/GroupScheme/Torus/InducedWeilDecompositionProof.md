# Induced tori as Weil restrictions from intermediate-field products

Workers 1548 and 1550. The theorem `inducedTorusWeilDecomposition` proves the
exact public proposition `InducedTorusWeilDecompositionStatement.{u}`. It retains
arbitrary universe `u`, arbitrary characteristic, the prescribed finite Galois
splitting field `L`, and the empty-product case. Neither the statement pair nor
its imported public files is changed.

The proof first applies `IsInducedTorus.exists_permuted_basis` to obtain a finite
permuted integral basis of the actual character lattice over `L`. This step
compares the witness field in the induced-torus predicate with `L` inside an
algebraic closure, using bijective restriction of split character lattices.

The action on basis indices defines a finite Galois set. For each orbit, the
fixed field of the stabilizer supplies an intermediate field. The orbit
construction identifies the disjoint union of their embeddings into `L`
equivariantly with the basis index set and numbers the fields by `Fin n`.
The proof uses `ULift.{u} (Fin n)` while applying the product-coordinate helper,
so its factor index lies in the field universe. `Equiv.sigmaCongrLeft` transports
the embedding-index equivalence along `Equiv.ulift`.

The actual Weil restriction from their product splits over `L` in these
embedding coordinates. Its character equivalence sends canonical Galois
transport to inverse postcomposition on the embedding indices.
`coordinateEquiv_equivariant_of_permuted` identifies those integer coefficient
functions with the chosen basis of the original torus, with exactly the same
action. Composing the two equivalences gives an equivariant equivalence of
actual character lattices.

Both groups are split over `L`. The finite-Galois character descent theorem
realizes this equivalence by an isomorphism over `k` to the lifted-index product.
`AlgEquiv.piCongrLeft` identifies that algebra with the product indexed by
`Fin n`, and `WeilGm.commCongrIso` supplies the final isomorphism required by the
public statement. All finite constructions permit an empty index set, so no positive-rank
or nonempty-factor hypothesis enters the argument.

This proof is an internal derivation using the named supporting constructions.
Worker 1550 authored the prescribed-field basis transport, compositional
character restriction, and finite permutation-basis coordinate equivalence.
Worker 1548 authored the orbit-field realization, product-Weil character
comparison, finite-Galois character descent, and this final assembly.
