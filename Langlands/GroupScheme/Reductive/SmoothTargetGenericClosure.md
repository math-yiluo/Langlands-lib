# The smooth generic closure of a reductive monomorphism

Worker 671.

This internal construction considers a reductive group `M` over a Dedekind
domain `R`, a smooth affine group `G`, and a homomorphism `f : M → G`
monic on underlying schemes. The chosen field `K` is a fraction field of `R`.
All objects lie in an arbitrary universe `u`.

The module constructs the schematic closure of the generic image using the
published `GenericSubgroupClosure` construction. Its canonical map from `M`
is schematically dominant. The reductive immersion theorem makes it an
immersion, and a quasi-compact schematically dominant immersion is open.
`imageOpen` is its actual open range and `openIso` identifies `M` with that
open subscheme, compatibly with the inclusion.

The closure is flat and locally of finite type by the published generic
closure construction. In each actual residue-field fibre it contains the
smooth source fibre as an open subgroup. The published theorem
`smooth_of_smooth_open_subgroup` makes each fibre smooth, and the flat
fibre criterion gives smoothness of the closure.

For every point of `Spec R`, `geometricFiberIdentityIso` identifies the
geometric fibre of `M` with the actual identity component of the geometric
closure fibre. The base-changed factor is open by stability under base change.
It is also closed by the field theorem for monomorphisms from smooth connected
affine groups. The characterization of the identity component by a connected
open and closed subgroup gives the displayed group-scheme isomorphism.
Reductivity of the geometric source fibre transports across its inverse.
Consequently `identityComponentReductiveLocus_eq_univ` proves that every
geometric identity component of the closure is connected reductive.

The construction and the affine, monic and schematic-dominance properties of
the factor use only a flat affine source locally of finite type. The open
immersion, smoothness, open-image isomorphism and geometric identity-component
results assume `IsReductive M`.

This is an internal composition of published constructions and the separately
submitted reductive immersion theorem. It does not prove connectedness of
the closure's special fibre or global closedness of `f`. In particular it
does not assume or prove `ConnectedFibreLocusClosedStatement`.
