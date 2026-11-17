# Assembling coroot quotient maps from local coefficient rings

This internal unit reduces the relative derived-group existence problem to an
actual coroot quotient construction over local coefficient rings and the
separate relative semisimple perfectness input. It proves the passage from
local rings to arbitrary coefficient rings, including smoothness, surjectivity
and semisimplicity of full geometric kernels. Both remaining inputs stay
explicit; this unit does not prove the unconditional existence theorem.

`RelativeDerivedLocalCorootQuotientExistenceStatement` quantifies over every
supplied affine pinned model `M` whose coefficient ring is local, with a
decidable equality on its finite coordinate type. It asks for a homomorphism
from `M.group` to the actual diagonalizable group attached to the integral
annihilator of all coroots, restricting on `M.inclusion` to the actual
`corootProjection`. It imposes no smoothness or surjectivity condition on this
homomorphism. Decidable equality supplies coordinate constructions; the
derived existence conclusions use classical decidability internally.

The helper `Dynamic.comp_eq_one_of_mem_unipotent_to_comm` says that a
homomorphism to a separated commutative group kills every dynamic unipotent
point. Functoriality puts the image in the target dynamic unipotent subgroup.
Commutativity also puts it in the target centralizer, and uniqueness of the
identity limit forces it to be the identity. This argument holds on every
relative scheme test.

`RelativeDerived.pullbackPointHom` transports a supplied homomorphism on a
pullback to the corresponding original-base point groups through the actual
pullback point equivalence. A supplied target isomorphism normalizes its
target. `pullbackPointHom_restrict` preserves a prescribed restriction, and
`pullbackPointHom_unipotent` kills original dynamic unipotent points by
dynamic base-change compatibility. The triple-cell lemma combines these
facts: the two outer factors are killed and the middle factor is evaluated
by the prescribed torus map.

`cellCompatible_dynamic_of_localCorootQuotient` applies this formula to the
canonical cocharacter of a supplied affine pinned model, with any
representatives of its positive and negative dynamic unipotents. It takes
the open-immersion premise for their triple-cell multiplication explicitly.
The cell target map is projection to the middle coordinate torus followed
by the coroot projection.

Compatibility is checked on spectra of all commutative local rings using
`CellGluing.cellCompatible_of_localRingPoints`. Such tests detect morphisms
into affine schemes through actual local stalks, including nilpotents.
For a local-ring point of the original base, the affine Spec correspondence
supplies an algebra structure. The full scalar-extended pinned model admits
the local quotient witness. The canonical split-torus and diagonalizable
base-change square puts its torus restriction in the form needed by
`pullbackPointHom`. Applying that point homomorphism to a cell product
relation proves the desired relation in the target. The chosen local
witnesses need no naturality in their coefficient rings.

`exists_smooth_corootQuotient_of_local` proves that every supplied affine
pinned model, over an arbitrary coefficient ring, has an actual
homomorphism `q` to its coroot quotient with

- its exact prescribed torus restriction;
- smoothness of its underlying scheme morphism;
- surjectivity of that scheme morphism.

The proof uses the canonical affine representatives of both dynamic
unipotents. The original coordinate torus represents the centralizer of the
canonical cocharacter, by `centralizer_originalCocharacter`. The
arbitrary-base dynamic triple-cell theorem gives the open immersion.
The established compatibility and the explicit cell unit permit
`CellGluing.glueHom` to construct `q`; the torus cell section proves its exact
restriction. Both unipotent factors are smooth, so the projection to the
middle torus followed by the smooth coroot projection is smooth. The
arbitrary-base theorem `smooth_of_smooth_openCell` then gives smoothness of
`q`. Its composite with the torus inclusion is the surjective coroot
projection, which gives surjectivity of `q`.

`relativeDerivedSplitTorusQuotient_of_localCorootQuotient` adds the relative
torus condition and semisimplicity of every full geometric kernel using
`isSemisimple_corootQuotient_geometricKernel`. It proves the split quotient
existence input. Finally,
`relativeDerivedGroupExistence_of_localCorootQuotient` combines that result
with the existing affine pinned atlas and admissible-subgroup descent
reduction. Its two arguments are precisely the local construction statement
and `RelativeSemisimpleFppfPerfectStatement`.

All constructions are uniform in the universe. The arbitrary-ring and
arbitrary-scheme conclusions have no noetherian, reducedness, nonempty-base,
quasi-compactness or characteristic premise. Their conclusions concern
actual scheme morphisms and complete scheme-theoretic kernels.

The provenance is internal: the new local input is a restricted construction
problem, and the proved implications assemble the existing scalar-extension,
dynamic subgroup, cell-gluing, quotient geometry, geometric-kernel and
descent APIs. No parent relative derived-group existence or uniqueness
theorem is assumed. The coroot cell extension geometry and geometric-kernel
prerequisite pairs are reused unchanged from their separate submissions.
