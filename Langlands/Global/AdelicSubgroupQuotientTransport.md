# Actual subgroup rational quotients under group-scheme isomorphisms

This internal construction transports the existing actual rational subgroup
quotients and their intrinsic compact-quotient probability measures along
an isomorphism of group schemes.

The input is a number field `F : Type u`, actual affine group schemes `G`
and `H` over `Spec F`, an isomorphism `e : G ≅ H`, and a subgroup functor
`V` of `H`. The source subgroup functor is the existing inverse image
`V.comap e.hom`. The first coefficient-group construction does not require
affineness. None of these constructions requires the subgroup functor
to be represented, normal, commutative, unipotent or parabolic.

`coefficientSubgroupIso` restricts the group-valued Yoneda point isomorphism
to the subgroup and its inverse image on each coefficient algebra.
`adelicSubgroupIso` specializes this map to the full adele ring. Continuity
of postcomposition by `e.hom` and `e.inv` supplies the multiplicative
homeomorphism for the existing inherited adelic point topologies.
`adelicSubgroupIso_rational` uses principal-map naturality to identify
the actual restricted principal maps. Surjectivity of the rational
coefficient isomorphism then proves the exact principal-image membership
equivalence.

`rationalQuotientIso` descends this adelic map to the original left quotients
by those principal images, with their existing quotient topologies. Its
formula on representatives is proved, as is the positive translation law:
the image of `q * x` is the translate of the image of `q` by the image of
`x`. No quotient group structure or normality is used. Closedness of the
target evaluated adelic subgroup pulls back to the source subgroup, and
compactness of the target rational quotient transfers through the inverse
homeomorphism.

For the measure results both group schemes are also locally of finite
type. The target evaluated adelic subgroup is assumed closed, and its
actual rational quotient is assumed compact. The preceding transport
lemmas derive these two properties on the source; they are not separate
inputs. Closedness and the existing ambient results give locally compact
Polish subgroup topologies. The existing principal discreteness theorem
identifies the inherited quotient measurable structures as Borel.

`measurePreserving_rationalQuotientIso` proves that the constructed quotient
homeomorphism carries
`normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)` exactly to
`normalizedRationalQuotientHaarMeasure F H V`. These are the existing
intrinsic mass-one measures. The proof pushes the source probability
forward, transports regularity, and conjugates every positive right
translation through the constructed map. Right invariance of each
unchanged measure comes from
`compactCompatibleNormalizedRationalQuotientMeasure`, which already
derives the necessary analytic Haar right invariance from compactness.
On the target principal subgroup the proof uses its actual discrete
counting Haar measure. The existing
`exists_pos_smul_eq_of_rightInvariant_quotient` identifies the two regular
nonzero invariant quotient measures up to a positive finite real scalar.
Their total masses are both one, so that scalar is one.

`measurePreserving_rationalQuotientIso_symm` gives the inverse transport.
For every complex-valued function on the target quotient,
`integrable_comp_rationalQuotientIso_iff` separately equates Bochner
integrability with integrability of its pullback. The subsequent
`integral_comp_rationalQuotientIso` is the corresponding integral identity.
That identity also holds for totalized integrals; convergence is asserted
only by the separate equivalence or an integrability premise supplied
by a consumer.

The provenance is internal: the module combines the published actual
coefficient-point, subgroup inverse-image, principal-map, quotient
homeomorphism and invariant-measure uniqueness APIs. It makes no new
claim attributed to an original literature passage. In particular,
it assumes neither a Haar modulus nor a measure identity as input.
It does not identify the image of a particular parabolic radical under
rational conjugation, prove rational classification of parabolics,
establish an iterated-period formula, prove general reductive finite
volume or supply a cuspidal-space equivalence. Those remain separate
obligations of the consuming constructions.
