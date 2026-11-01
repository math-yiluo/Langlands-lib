# Descending maps between actual operator quotients

This internal derived construction supplies maps between the existing actual
`OperatorSubquotient` presentations. The number field has arbitrary universe,
the matrix rank is any natural number, and the coefficients are complex.
There is no CM-field or character hypothesis.

For actual quotients `Q` and `T`, `compatibleMaps` is the complex submodule of
all genuine whole-operator intertwiners from `Q.upper` to `T.upper` which send
`Q.lower` into `T.lower`. The closure proofs use the actual target denominator's
submodule laws.

`map` descends such an intertwiner `L` by applying the published `Q.lift` to
`T.projection.comp L`. The target projection's exact kernel proves that this
composite kills the source denominator. This reuses the whole-operator
covariance already proved for `lift`, whose underlying linear map is Mathlib's
`Submodule.liftQ`; here it is the usual quotient map `Submodule.mapQ`.
It sends the class of `f` to the class of `L f`. `map_projection` is the exact formula on
every numerator vector. `map_naturality` expresses equality of the two
composites with the actual quotient projections. `map_unique` proves uniqueness
among all genuine quotient intertwiners satisfying that formula by the published
lift uniqueness law.

`mapLinear` bundles descent as a complex-linear map on the entire compatible
numerator-map submodule. Its addition and scalar laws follow from the actual
target projection's linearity and uniqueness of the descended map.
The descended identity is the identity. The descended composite is the
composite of the descended maps, with preservation of the denominators
proved by composition. No category instance is added.

`map_projection_eq_zero_iff` tests zero on each source representative by
membership of its numerator image in the target denominator.
`map_eq_zero_iff` says that the entire descended map is zero exactly when
every numerator image belongs to that denominator. Surjectivity of the
source projection proves the converse.

`map_injective_iff` says that the descended map is injective exactly when
membership of `L f` in the target denominator implies membership of `f`
in the source denominator. The forward direction applies injectivity to
the projected vector and zero. The converse uses the zero-kernel criterion
for linear maps and the exact kernel of the actual source projection.
It does not require numerator injectivity.

`map_surjective` descends a supplied surjective numerator map.
`map_surjective_iff` gives the more precise criterion: every target numerator
vector `v` differs from some `L w` by a vector in the target denominator.
Both directions choose representatives through the actual canonical
projections and use the target projection's subtraction law and exact kernel.

`mapEquiv` constructs a genuine equivalence of the entire quotient actions
when numerator surjectivity and reflection of denominator membership are
supplied. Its underlying intertwiner is the constructed `map`, and its
formula on every projected numerator vector is exact. These assumptions
are enough; numerator injectivity is not required.

Provenance is internal. The constructions specialize Mathlib's actual module
quotient map to the already published actual automorphic numerator and
denominator data, reusing the published quotient lift and its intrinsic
whole-operator covariance for the projection composed with the supplied
genuine numerator map. The remaining proofs use canonical quotient
surjectivity, exact kernel membership, linearity and the genuine intertwiner
equivalence construction. The existing representation-subfunctor quotient
construction is related: it descends all functor morphisms that preserve two
subfunctors. This module instead accepts two fixed automorphic presentations
and any supplied compatible numerator intertwiner.

These constructions do not assert that every map of quotient representations
lifts to a numerator map, identify dependent presentations, or construct
nonzero or irreducible spectral constituents. No quotient topology or
function evaluation is added.
