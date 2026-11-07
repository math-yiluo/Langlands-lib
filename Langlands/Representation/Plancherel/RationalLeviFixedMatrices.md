# Fixed matrices under the actual rational normalization comparison

This internal derived construction applies the published full-parabolic to
positive Levi normalization comparison to each actual unramified fiber.
The geometric radical and compatible root presentation supply radical
unimodularity by `parabolicRadical_isUnimodular`; it is not an additional
premise. The actual two fibers are equivariantly isomorphic and have the
same irreducibility predicate.

The field has arbitrary characteristic and universe `u`; the smooth Levi
representation has independent carrier universe `uV`. The ambient group is
literally `rationalPoints G` with its canonical rational-point topology.
Affineness of `G` and `M`, local compactness and the nonarchimedean group
structure are retained. The inputs include the displayed actual semidirect
decomposition, closedness of its unipotent image, connected reductivity of
`G`, and geometric unipotent-radical status of `n`. Every parameter belongs
to the full complex unramified character group for the actual rational norm
characters of `r`. No admissibility or unitarity premise is needed here.

`inducedLeviNormalizationEquiv` applies `normalizedInductionLeviEquiv` to
the actual unramified twist of the given representation. Its source is
`complexInduced`, normalized with the positive full-parabolic half-modulus;
its target is `UnramifiedLeviInduction`, obtained by the positive Levi
half-modulus twist before inflation. The companion theorem
`inducedLeviNormalization_irreducible_iff` uses this equivalence and its
inverse to transport irreducibility in both directions.

A compact-open fixed-space basis is transported along the restriction of
that equivalence to fixed vectors. Naturality of the actual normalized
Hecke projection identifies its compressed matrices with those of the
original full-normalized fiber. This calculation applies to arbitrary
representation equivalences and uses the same Haar measure, subgroup and
ambient element.

More precisely, `Compact.fixedMatrix_mapBasis` works for independent group,
source-carrier, target-carrier and finite index universes. The group is a
topological group with a Borel measurable structure and a left Haar
measure; the two representations are smooth. The subgroup is open and
compact. Intertwining first moves the translated basis vector through the
equivalence; `Hecke.fixedProjection_intertwiner` moves its normalized
projection through the equivalence; the coordinate map of the transported
basis then cancels the fixed-vector equivalence. `leviFixedBasis` and
`leviFixedBasis_matrix` specialize this calculation to the actual
normalization comparison. The basis construction itself permits any index
type; finiteness is required only for the matrix statement.

The construction supplies neither a basis nor matrix continuity by itself.
It asserts no irreducible parameter or uniform subquotient detection and
does not prove the host generic irreducibility theorem.
