# Actual good opens and conditional openness

This module internally assembles actual good neighbourhoods and the exact
arbitrary-base openness conclusion from five explicit universal structural
statements. It works in every universe `u` for every scheme base `S` and every
smooth affine group scheme `G`. Fibres may be disconnected and the base need
not be Noetherian. No restriction on characteristic is imposed.

The selected definition,
`identityComponentReductiveNeighbourhood_of_lifting_and_fieldStatements`, takes
an original point `s` in the reductive geometric identity-component locus. Its
result is an actual open subset of `S` containing `s` and contained in the same
original locus. An initial relative torus or a family of good opens is not
assumed.

The constructor first applies
`exists_finiteGalois_hasSplitMaximalTorus` to the actual canonical residue fibre
of `G`. The imported proofs `torusFiniteGaloisSplitting` and
`maximalTorusBaseChange` discharge that theorem's splitting and maximality
premises. This gives a split maximal torus over a finite Galois extension `K` of
the actual residue field. Its inclusion is initially in the successive actual
pullbacks. The inverse actual composition isomorphism transports it to the
actual `K`-valued fibre over the original base.

`etaleResidueExtension` realizes `K` with its given scalar structure as the
residue field of a point in an actual etale neighbourhood. Pullback along the
inverse residue comparison and the actual `groupFibreIso` transports the same
torus inclusion into the canonical residue fibre of the pulled-back group.
The imported residue-fibre helpers prove its splitness and maximality. The
unchanged locus base-change identity, together with `point_over`, proves locus
membership at this new point.

The existing
`identityComponentReductiveNeighbourhood_of_splitMaximalResidueTorus` then uses
the explicit relative split-torus lifting statement and the four explicit field
statements to construct a good open at that new point. Finally, its image under
the etale projection is open, contains `s`, and lies in the original locus. This
is the returned neighbourhood.

The theorem
`identityComponentReductiveLocusOpen_of_lifting_and_fieldStatements` applies this
actual constructor at every locus point and uses the ordinary pointwise
criterion for an open set. Its conclusion is precisely
`IdentityComponentReductiveLocusOpenStatement.{u}`. Its five retained inputs are
`RelativeSplitTorusLiftingStatement`,
`AlgClosedMaximalTorusCentralizerStatement`,
`RelativeRootReflectionExistenceStatement`, `RootReducednessStatement` and
`SplitRootLieLineStatement`, each in universe `u`. The resulting implication is
conditional. This module does not prove these inputs or the unconditional
universal openness proposition. Finite Galois splitting, maximality base change,
etale realization, actual fibre comparisons and open descent are supplied by
the imported Library proofs rather than retained as further premises.

The provenance is internal: this is a composition of the cited Lean
constructors and transports, with the implemented proof route described above.
It introduces no new assertion from external literature.
