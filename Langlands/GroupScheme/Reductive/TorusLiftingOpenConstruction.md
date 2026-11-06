# Open neighbourhoods from actual split-torus lifting

This module is an internal composition of the existing actual torus-lifting
statement, field-point neighbourhood construction and open descent. It works
uniformly in universe `u`, over any scheme `S`, for a smooth affine group scheme
`G`. Ambient fibres may be disconnected; no characteristic or Noetherian
assumption is imposed.

`identityComponentReductiveNeighbourhood_of_splitTorus_fieldPoint` accepts an
actual commutative relative split torus with a closed inclusion into `G`, maximal
at the supplied field-valued point, and membership of its image in the original
reductive identity-component locus. A split presentation identifies the supplied
torus with a standard split torus. Precomposition by its inverse transports
closedness and maximality to that standard torus. The existing arbitrary-base
field-point constructor then gives an actual open neighbourhood of the same
original point, contained in the original locus. The field need not be
algebraically closed.

`isMaximalTorus_of_lifting_recovery` uses the exact inclusion-recovery equation
appearing in `RelativeSplitTorusLiftingStatement`. Its ambient isomorphism is the
inverse actual base-change-composition isomorphism followed by the equality
comparison for the specified residue point. After precomposing the original
maximal torus by the supplied source isomorphism, the recovery equation identifies
it with the lifted field-fibre inclusion followed by this ambient isomorphism.
Ambient isomorphism invariance therefore proves maximality of the actual lifted
inclusion. This helper adds no lifting or reductivity assumption.

The selected definition,
`identityComponentReductiveNeighbourhood_of_splitMaximalResidueTorus`, accepts a
specified actual split maximal torus in the canonical residue fibre at `s` and
assumes `s` is in the original locus. Applying the explicit relative lifting
statement produces an etale neighbourhood, a residue-field-valued point, an
actual relative split torus and a closed inclusion recovering the original one.
The split torus is bundled as commutative using its splitness. The preceding
helper recovers maximality at the specified lifted field point. The point lies
over `s` by the lifting equation. The exact locus base-change identity supplies
locus membership there. The split-presentation constructor gives a good open on
the etale neighbourhood; its image under the etale open map is the returned good
open on the original base, containing `s` and contained in the unchanged locus.

All neighbourhood constructors retain the universal maximal-torus centralizer,
forward root reflection, root reducedness and root Lie-line statements as
explicit inputs. The selected definition also retains the universal relative
split-torus lifting statement. The source residue torus is supplied, rather than
assumed to exist as part of this module's conclusion. These are substantive
conditional intermediate constructions. They do not prove the universal
openness statement or discharge any of the retained structural statements.
The proof route and definitions are internal compositions of the imported
Library declarations; no new external mathematical assertion is introduced.
