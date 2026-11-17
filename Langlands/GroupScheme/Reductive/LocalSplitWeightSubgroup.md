# Nonnegative weights independent of the regular cell cocharacter

Author: Worker 204.

This internal extension of `LocalSplitHeightSubgroup` works over any
commutative ring and on every scheme test over its spectrum. Its input
is the existing open split-cell chart, additive root maps equivariant
under the split torus, and a regular cocharacter `ν` whose pairings are
strictly negative on the listed negative roots and strictly positive
on the listed positive roots.

A second cocharacter `wt` measures the weights. It need not be regular
or equal to `ν`. For `exists_posComm_eq_weight_ge_of_regular`, only its
two input-root pairings must be nonnegative. The existing universal
commutator construction uses `ν`, while torus equivariance constrains
the same polynomials for `wt`. The existing coefficient vanishing
theorem then kills every coordinate whose `wt`-weight is below the
sum of the input weights. Evaluation at two global sections gives
the claimed ordered commutator formula on an arbitrary scheme test.

For the remaining declarations, every listed positive-root pairing
with `wt` is supplied as a natural weight `w p`. Zero weights are
allowed. `commutator_rootFactor_le_of_regular` gives the standard
group commutator sum bound for these weights. The existing
`posComm` convention is converted to `a * b * a⁻¹ * b⁻¹` by
exchanging and negating the parameters. In the resulting ordered
product, every factor below the sum has zero parameter; every
other factor belongs to the generated level.

At any positive cutoff, `mem_heightSubgroup_iff_of_regular` applies
`HeightFiltration.exists_coords_of_pos`. A level element has ordered
coordinates trivial below the cutoff. Choosing root parameters and
replacing the lower ones by zero gives supported section coordinates.
Conversely, the supported ordered product belongs to the generated
level factor by factor.

`positiveHeightCoordinatesEquiv` packages this characterization and
the existing split-cell injectivity as a bijection from supported
section vectors to the actual positive-height point subgroup.
It is an equivalence of types. The full ordered chart is not asserted
to be a homomorphism.

The provenance is derived from the existing universal-polynomial
construction, all-test specialization, weight vanishing and positive
cutoff collection. This unit separates the roles of the two
cocharacters without asserting the existence of suitable split-cell
data for a supplied parabolic or the descent of its filtration.
