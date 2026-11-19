# Irreducibility of archimedean standard-module components

The real and complex reductions choose an irreducible stable subspace of the
cuspidal realization at the place. The `PlaceComponentIsotypy` module gives
isotypy of the ambient realization with this subspace as its irreducible
constituent. The place parameter gives an injective linear map intertwining
the compact group and the real Lie directions. Complex linearity extends the
Lie intertwining to the full complexification by tensor induction. The
criterion in `GKIsotypicIrreducibility` then proves irreducibility from a
nonzero vector of the standard module that is scaled by every compact-equivariant
endomorphism.

At a real place, the compact model uses products of compound matrices in
coordinates that diagonalize the rotation of every induction block. The
Fourier cutoffs and sign parities constrain the number of occurrences of
each coordinate. Equality in these bounds forces the supported configurations
to be the ones obtained by independently choosing one of the two coordinates
in each induction block. Reflections give a one-dimensional space of
qualifying linear forms on these configurations. Extending compact
coefficients of a nonzero such form supplies the required vector.

For the complex place, `complexStandardExistsCompactScalarVector` supplies
this vector by transporting a minor monomial from a list sorted by its
character weights. The compact equivalence preserves the scalar action
condition, so the proof applies to the parameter in its given order.

The theorem `cuspidalArchimedeanStandardIrreducible` combines the two
reductions for the given place parameters. It proves the irreducibility
proposition of `CuspidalArchimedeanComponentStatement`.

The statement formalizes the irreducibility of the archimedean factors in
Getz–Hahn, *An introduction to automorphic representations*, §11.4,
pp. 300–302 (PDF pp. 311–313), displays (11.14)–(11.17), registered as
`getz-hahn-2024-automorphic-representations`. The proof uses the isotypy
argument of Flath, *Decomposition of representations into tensor products*,
proof of Theorem 1, p. 180 (PDF p. 176), and the archimedean formulation in
Theorem 3 and its discussion, pp. 181–182 (PDF pp. 177–178), registered as
`flath-1979-tensor-products`. The compact coefficient arguments are internal
constructions for the Library's standard-module models.
