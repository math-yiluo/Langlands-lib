# Measure support for lower-block quotient disintegration

This internal helper supplies the right triangular Haar measure, positive
finite compact open parameter volumes, and the analytic consequences of a
positive scaled pushforward identity. It is derived from the published
`LowerBlockQuotientDisintegrationStatement` and Mathlib measure theory.
It does not prove that statement or its lower-block measure identity.

## The right Haar measure

`Langlands.GeneralLinear.lowerTriangularSubgroup_isClosed` proves that
invertible lower triangular matrices form a closed subgroup: each required
matrix entry is zero, and the value map on matrix units is continuous.
It works over any commutative Hausdorff topological ring; no continuity of
ring operations is needed.

For every prime, p-adic field in its independent universe, supplied
`TopologicalData T`, and rank `d`, `lowerTriangularRightHaar F T d` is the
inversion pushforward of Mathlib's left Haar measure on the actual subgroup
`lowerTriangularSubgroup d F.Carrier`. Its measurable structure is the Borel
structure of the subgroup topology inherited from the matrix unit group.
Closedness supplies local compactness; the supplied field topology supplies
Hausdorffness and second countability.

`lowerTriangularRightHaar_properties` proves regularity, sigma finiteness,
positivity on every nonempty open set, finiteness on compact sets, and right
invariance. These follow from the corresponding left Haar properties and
the inversion homeomorphism. For every compact open subgroup `K`, openness
and the identity element give positive mass, while compactness gives finite
mass. This construction applies also to rank zero. It imposes no numerical
normalization, and right invariance does not require unimodularity.

## Additive parameter volumes

`rectangularMeasure_compactOpen_pos_lt_top` treats every scalar
`AdditiveHaarMeasure`, every pair of natural ranks, and every compact open
additive subgroup of the actual rectangular matrix space. The rectangular
measure is the published iterated product of the supplied scalar measure.
The supplied field's second countability gives scalar sigma finiteness,
so the published product Haar instance applies. Positivity follows because
the subgroup is open and contains zero; compactness gives finiteness.
The matrix measurable structure remains its iterated product structure.

## Positive scaled measure transfer

`complex_integral_transfer_of_positive_scaled_map` is a generic consequence
of an explicitly supplied identity
`μ = ENNReal.ofReal C • Measure.map chart ν`, with `C > 0` and measurable
`chart`. For every measurable complex function it proves the equivalence
of integrability for `μ` and integrability of the composite for `ν`.
It also proves the exact complex integral formula, even for totalized
nonintegrable Bochner integrals. The proof uses positive finite measure
scaling, integrability under a measurable pushforward, and the Bochner
pushforward and measure scaling formulas. The scalar becomes `(C : ℂ)`
by the real scalar action on complex numbers.

The scaled measure identity is a hypothesis of this generic helper. No
lower-block Jacobian, conullness, open embedding, quotient-measure
comparison, or normalization assertion is proved or assumed as a
property of the actual lower-block chart here. Those remain obligations of
the parent disintegration proof.
