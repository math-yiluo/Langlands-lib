# Local split coordinates aligned with a supplied maximal torus

This is an internal refinement of the Library's
`etaleLocalSplitReductive`, used to retain the given torus in the local
argument for isogeny rigidity. The construction uses the published
relative-torus definition, fibrewise maximality transport, open coordinate
root-datum theorem and principal root-weight trivialization theorem. It
introduces no additional source theorem or hypothesis on the base.

`HasSplitMaximalTorusCoordinates i` concerns an inclusion from a supplied
commutative group scheme into an affine group scheme over `Spec R`. It
asserts the existence of a finite coordinate index type and an actual
group-scheme isomorphism from that coordinate split torus to the supplied
source. The resulting coordinate inclusion is closed and fibrewise
maximal. It has a single full reduced root datum on the coordinate lattices
that realizes the actual root datum on every supplied field algebra, and
each actual root-weight module over `R` is free of rank one.

`HasSplitMaximalTorusCoordinates.of_isos` transports these data along
compatible source and ambient isomorphisms. The coordinate source
isomorphism changes by composition; the root datum stays the same, and the
root-weight modules are identified by `exponentWeightAmbientEquiv`.

`exists_affine_open_splitCoordinates_of_coordinateTorus` starts with a
closed coordinate split torus that is maximal on every residue fibre in a
reductive group. Near any chosen base point, the open coordinate root-datum
theorem gives one full reduced datum. Principal localization makes all its
finitely many root-weight modules free simultaneously. The given torus
map is pulled back along that localization and identified with the new
coordinate torus by the canonical base-change isomorphism.

`exists_etale_affine_splitCoordinates_of_suppliedTorus` applies to every
scheme, a reductive group, and a supplied closed relative torus maximal on
every residue fibre. It returns an affine étale neighbourhood of each base
point with `HasSplitMaximalTorusCoordinates` for the pullback of that very
inclusion. The proof selects a member of the torus's defining étale
splitting cover, takes an affine open neighbourhood, and applies the
preceding principal-localization construction. Naturality of the
base-change composition isomorphism identifies the successive pullback
of the original inclusion with its direct pullback.

These results supply local coordinates. They do not assert compatibility
of an isogeny with root data or existence of local torus conjugators.
