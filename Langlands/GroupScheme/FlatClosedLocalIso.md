# Isomorphisms near a fibre for flat closed group inclusions

`Langlands.GroupScheme.FlatClosedLocalIso.isIsoNear_of_residueFiber` proves
that a closed group-scheme inclusion which is an isomorphism on one residue
fibre becomes an isomorphism over an open neighbourhood of that base point.
The source structure map must be flat and locally of finite presentation.
The target structure map must be locally of finite type and have geometrically
connected fibres. There is no smoothness, affineness, quasi-compactness or
Noetherian hypothesis. The conclusion is the existing
`SmoothMonoLocalIso.IsIsoNear` predicate: an actual open containing the point,
with the actual base-changed underlying scheme map an isomorphism.

This is an internal extension of the published `SmoothMonoLocalIso`
construction. Closedness permits a weaker target hypothesis: the final fibre
surjectivity argument uses an image that is both open and closed in a connected
space, and does not require target smoothness or irreducibility.

## Implemented proof

The first helper,
`Langlands.AlgebraicGeometry.flat_stalkMap_of_flat_residueFiber_of_lft_target`,
proves stalk flatness of a morphism over the base from flatness of the residue
fibre at the specified source point. Its source is flat and locally finitely
presented over the base, and its target is locally of finite type. The local
fibrewise flatness criterion from the published commutative-algebra development
requires essential finite presentation of the source stalk over the base
stalk, essential finite type of the target stalk, and flatness of the source
over the base. These follow from the stated assumptions. Flatness of the
residue-fibre map gives the fibre-stalk input through the published
`fiberStalkFlatness` comparison. The implementation follows the existing
flat-stalk proof with the target's stronger local finite-presentation premise
replaced by the local finite-type premise actually used in that proof.

A closed inclusion is a monomorphism. Local finite presentation of the source
and local finite type of the target give local finite presentation of the
inclusion by `SmoothMonoLocalIso.locallyOfFinitePresentation_hom`. At a base
point whose residue-fibre map is an isomorphism, that fibre map is flat. The
flat-stalk helper applies at the source unit. A monomorphism is formally
unramified; flatness and essential finite presentation then imply formal
etaleness of the stalk map. Thus the base point belongs to the open
`SmoothMonoLocalIso.unitEtaleOpen`.

On this open, the etale locus of the inclusion supplies a flat family over
the base that meets every unit. The published group-translation argument
`SmoothMonoLocalIso.flat_of_flat_family` proves flatness of the whole
restricted inclusion. Flatness and the monomorphism property, together with
local finite presentation, make it an open immersion. It remains a closed
immersion after restriction.

The helper `isIso_of_flat_of_closed` proves surjectivity. After pullback to
each residue field, the target is connected and the image is both open and
closed. The source fibre is nonempty because its group unit defines a point.
Consequently the image is the entire target fibre. Pullback-point existence
transfers this fibrewise surjectivity to global surjectivity. A surjective
open immersion is an isomorphism, which proves the result on the chosen open.

This module supplies the geometric step used by
`Torus.SuppliedCentralizerSpreading`. It does not assert smoothness of any
arbitrary centralizer or conclude affineness of the ambient group.
