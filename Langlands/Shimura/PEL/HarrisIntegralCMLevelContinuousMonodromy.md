# Continuous actual Harris monodromy from an invariant compact open level

This internal construction retains the actual integral-action family, full Weil
frames, geometric point, and actual Tate and Tate-twist monodromy prerequisites
of `HarrisIntegralCMLevelMonodromy`. It is conditional on a chosen full frame
whose raw orbit at one compact open level is invariant.

The underlying frame is linear over the finite adeles. Its forward map is
continuous from the canonical module topology on the scalar extension to the
actual rational Tate topology: the source has the module topology, while the
target has continuous addition and scalar multiplication by the published Tate
topology theorems. No inverse-continuity assertion is needed.

Pointwise evaluation of the actual Harris frame-coordinate equivalence is
continuous, by continuity of the scalar-extension group evaluations and the
forward frame map. It is injective because full frames are subtypes of linear
equivalences; the twist trivialization is existential, not extra frame data.

An invariant raw orbit at `U` puts all monodromy coordinates in the compact
subgroup `U`. Restrict the pointwise evaluation map to `U`. The rational Tate
target is Hausdorff, so the resulting continuous injective map from a compact
space is an embedding. Composing actual monodromy with frame evaluation is
pointwise continuous by the published actual rational Tate monodromy theorem.
The embedding therefore recovers continuity of the coordinate map into `U`,
and then into the original Harris group. The continuous homomorphism bundles
this continuity with the already proved algebraic monodromy laws.

The provenance is internal. No general homeomorphism theorem for arbitrary
adelic frames, no unconditional continuity, and no representing geometry is
assumed or asserted. The host representability target remains open.
