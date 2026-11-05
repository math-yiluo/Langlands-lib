# Integral models on the original coefficient-point carrier

Author: Worker 1641.

This internal adapter uses the existing actual group schemes and point
carriers. Let `k` and `L` be fields in an arbitrary common universe, with
an algebra structure `k → L`, and let `G` be a group scheme over `k`.
The existing `GaloisPointComparison.baseChangeCoeffEquiv` identifies
identity-test rational points of the actual base change `G_L` with the
original `G.affinePoints (CommAlgCat.of k L)`. It requires neither a
finite extension nor a Galois extension. Its underlying morphism is
composition with the first projection of the actual pullback.

The imported `baseChangeCoeffEquiv_map` applies the existing naturality theorem
for the multiplicative pullback correspondence. If `G` is affine and `L`
is a topological ring, `isHomeomorph_baseChangeCoeffEquiv` proves that the
same comparison is a homeomorphism from the existing named
`rationalPointTopology` to the existing regular-function evaluation
topology on coefficient points. The implemented proof composes
`rationalPointsAffineHomeomorph` for `G_L` with the inverse of
`affinePointsBaseChangeContinuousMulEquiv`. Their actual projection
formulas identify that composite with the already published
multiplicative comparison. The shared `baseChangeCoeffContinuousMulEquiv`
from `Rational/ScalarExtensionTopology` bundles this same map and its
continuity in both directions; this module reuses that construction.

Now let `R` be a domain with fraction field `L` and let `M` be an
`IntegralModel R L G_L`. The model already supplies an affine flat
finite-type group scheme over `R` and an actual generic-fibre
isomorphism. `coefficientPointMap` composes the model's integral-point
homomorphism with the existing generic-point comparison.
`coefficientPointMap_left` states its underlying scheme morphism: first
restrict the integral section along `Spec L → Spec R`, then use the
pullback lift and specified generic-fibre isomorphism, then project
`G_L` to `G`.

`coefficientIntegralPoints` is the range of that homomorphism, hence a
subgroup of the original coefficient-point group. Its membership lemmas
give an actual integral-section witness and the equivalent inverse-image
test in the model's existing `integralPoints`. The subgroup equals the
image of those integral points under the published multiplicative
comparison. A morphism of integral models extending a base-changed
homomorphism commutes with these coefficient-point maps, by the model's
existing naturality and the preceding generic comparison.

For affine `G` and a topological ring `L`,
`isCompact_coefficientIntegralPoints_iff` transfers compactness in both
directions through the homeomorphism.
`coefficientIntegralPoints_maximal` transfers maximality among compact
supergroups: pull a compact supergroup back under the homeomorphism,
apply the supplied maximality hypothesis on the actual rational-point
group, and use the membership equivalence to recover equality.
No topological hypothesis is needed for
`coefficientIntegralPoints_covering`. A supplied literal left product
of the range of a base-changed homomorphism and the model's integral
points is transported by the multiplicative point comparisons and
naturality to the same left product inside the original coefficient
points.

The provenance is entirely derived from the published actual
pullback-adjunction, rational-point topology, coefficient base-change
homeomorphism, and integral-model definitions and naturality. No external
structural theorem is asserted. In particular this adapter does not
construct a good integral model, prove a model's integral points maximal,
or establish its parabolic covering hypothesis. Those remain obligations
in the almost-everywhere integral Iwasawa family proof.
